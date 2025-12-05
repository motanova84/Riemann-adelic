#!/usr/bin/env python3
"""
Test suite for Hook C1 — Schatten-Paley Monitor.

This test suite validates the functionality of the SchattenPaley hook
in the noesis_guardian module.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import json
import pytest
import tempfile
from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from noesis_guardian.modules.hook_schatten_paley import SchattenPaley
from noesis_guardian.guardian_core import NoesisGuardian as GuardianCore, Notifier

# Create Status enum for backward compatibility
class Status:
    OK = "ok"
    WARNING = "warning"
    ERROR = "error"


class TestSchattenPaleyModule:
    """Test SchattenPaley module functionality."""

    def test_module_exists(self):
        """Verify module can be imported."""
        assert SchattenPaley is not None

    def test_run_with_valid_data(self):
        """Test run() with valid spectrum data."""
        # First check if data file exists
        data_path = Path(__file__).parent.parent / "data" / "spectrum_Hpsi.json"
        if not data_path.exists():
            pytest.skip("spectrum_Hpsi.json not found")

        result = SchattenPaley.run(str(data_path))

        assert "status" in result
        assert "Hilbert_Schmidt_norm" in result
        assert "Trace_norm" in result
        assert "Schatten_2" in result
        assert "Schatten_3" in result
        assert "message" in result

    def test_run_missing_data(self):
        """Test run() with missing data file."""
        result = SchattenPaley.run("/nonexistent/path.json")

        assert result["status"] == "missing_data"
        assert "Missing" in result["message"] or "missing" in result["message"].lower()

    def test_hilbert_schmidt_norm(self):
        """Test Hilbert-Schmidt norm calculation."""
        from mpmath import mp, mpf

        # Simple test case: eigenvalues [1, 2, 3]
        # HS = sqrt(1 + 4 + 9) = sqrt(14)
        eigs = [mpf(1), mpf(2), mpf(3)]
        hs = SchattenPaley.hilbert_schmidt_norm(eigs)

        expected = mp.sqrt(14)
        assert abs(hs - expected) < 1e-10

    def test_trace_norm(self):
        """Test trace norm calculation."""
        from mpmath import mpf

        # Simple test case: eigenvalues [1, 2, 3]
        # TR = 1 + 2 + 3 = 6
        eigs = [mpf(1), mpf(2), mpf(3)]
        tr = SchattenPaley.trace_norm(eigs)

        assert abs(tr - 6) < 1e-10

    def test_schatten_p_norm(self):
        """Test Schatten-p norm calculation."""
        from mpmath import mp, mpf

        # Test Schatten-2 (should equal Hilbert-Schmidt)
        eigs = [mpf(1), mpf(2), mpf(3)]
        s2 = SchattenPaley.schatten_p(eigs, 2)
        hs = SchattenPaley.hilbert_schmidt_norm(eigs)

        assert abs(s2 - hs) < 1e-10

    def test_schatten_p_invalid_p(self):
        """Test Schatten-p raises error for p < 1."""
        from mpmath import mpf

        eigs = [mpf(1), mpf(2)]
        with pytest.raises(ValueError):
            SchattenPaley.schatten_p(eigs, 0.5)

    def test_stability_detection(self):
        """Test that stability is correctly detected."""
        # Create temp file with stable eigenvalues
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".json", delete=False
        ) as f:
            data = {
                "eigenvalues": [1.0, 0.5, 0.25, 0.125, 0.0625]
            }
            json.dump(data, f)
            temp_path = f.name

        try:
            result = SchattenPaley.run(temp_path)
            assert result["status"] == "ok"
            assert "stable" in result["message"].lower()
        finally:
            Path(temp_path).unlink()

    def test_anomaly_detection(self):
        """Test that anomalies are correctly detected."""
        # Create temp file with very large eigenvalues
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".json", delete=False
        ) as f:
            data = {
                "eigenvalues": [1e10] * 100  # Will exceed threshold
            }
            json.dump(data, f)
            temp_path = f.name

        try:
            result = SchattenPaley.run(temp_path)
            assert result["status"] == "⚠️ anomaly"
            assert "anomaly" in result["message"].lower()
        finally:
            Path(temp_path).unlink()


class TestGuardianCore:
    """Test GuardianCore functionality."""

    def test_guardian_initialization(self):
        """Test GuardianCore initializes correctly."""
        guardian = GuardianCore()
        assert "schatten_paley" in guardian.hooks

    def test_hook_registration(self):
        """Test hook registration."""
        guardian = GuardianCore()
        guardian.register_hook("test_hook", lambda: {"status": "ok"})
        assert "test_hook" in guardian.hooks

    def test_run_hook(self):
        """Test running a specific hook."""
        guardian = GuardianCore()
        guardian.register_hook("test_hook", lambda: {"status": "ok", "value": 42})
        result = guardian.run_hook("test_hook")

        assert result["status"] == "ok"
        assert result["value"] == 42

    def test_run_hook_not_found(self):
        """Test running non-existent hook raises error."""
        guardian = GuardianCore()
        with pytest.raises(KeyError):
            guardian.run_hook("nonexistent_hook")

    def test_run_all_hooks(self):
        """Test running all hooks."""
        guardian = GuardianCore()
        report = guardian.run_all_hooks()

        assert "timestamp" in report
        assert "hooks" in report
        assert "overall_status" in report
        assert "anomalies" in report

    def test_get_schatten_paley_report(self):
        """Test getting Schatten-Paley report specifically."""
        guardian = GuardianCore()
        result = guardian.get_schatten_paley_report()

        assert "status" in result


class TestNotifier:
    """Test Notifier functionality."""

    def test_alert(self, caplog):
        """Test alert notification."""
        Notifier.alert("Test alert message")
        # Just verify it doesn't raise an error

    def test_info(self, caplog):
        """Test info notification."""
        Notifier.info("Test info message")
        # Just verify it doesn't raise an error

    def test_success(self, caplog):
        """Test success notification."""
        Notifier.success("Test success message")
        # Just verify it doesn't raise an error


class TestSchattenPaleyMathematicalProperties:
    """Test mathematical properties of Schatten-Paley analysis."""

    def test_exponential_decay_implies_finite_norms(self):
        """Test that exponentially decaying eigenvalues give finite norms."""
        import numpy as np
        from mpmath import mpf

        # Create exponentially decaying eigenvalues
        alpha = 0.5
        N = 100
        eigenvalues = [mpf(np.exp(-alpha * n)) for n in range(N)]

        hs = SchattenPaley.hilbert_schmidt_norm(eigenvalues)
        tr = SchattenPaley.trace_norm(eigenvalues)

        assert float(hs) < float("inf")
        assert float(tr) < float("inf")
        assert float(hs) > 0
        assert float(tr) > 0

    def test_schatten_norm_ordering(self):
        """Test Schatten norms decrease with increasing p."""
        import numpy as np
        from mpmath import mpf

        alpha = 0.3
        N = 50
        eigenvalues = [mpf(np.exp(-alpha * n)) for n in range(N)]

        s1 = SchattenPaley.schatten_p(eigenvalues, 1)
        s2 = SchattenPaley.schatten_p(eigenvalues, 2)
        s3 = SchattenPaley.schatten_p(eigenvalues, 3)

        # For trace class operators, Schatten norms decrease with p
        assert float(s1) >= float(s2) * 0.99  # Allow small numerical error
        assert float(s2) >= float(s3) * 0.99

    def test_hilbert_schmidt_equals_schatten_2(self):
        """Test Hilbert-Schmidt norm equals Schatten-2 norm."""
        import numpy as np
        from mpmath import mpf

        eigenvalues = [mpf(n) for n in [1.5, 2.3, 0.8, 1.2, 0.5]]

        hs = SchattenPaley.hilbert_schmidt_norm(eigenvalues)
        s2 = SchattenPaley.schatten_p(eigenvalues, 2)

        assert abs(float(hs) - float(s2)) < 1e-10


class TestIntegration:
    """Integration tests for the complete hook system."""

    def test_full_pipeline(self):
        """Test complete pipeline from data to report."""
        guardian = GuardianCore()
        report = guardian.run_all_hooks()

        # Should have run schatten_paley hook
        assert "schatten_paley" in report["hooks"]

        sp_result = report["hooks"]["schatten_paley"]
        # Should have a status (ok, anomaly, or missing_data)
        assert sp_result["status"] in ["ok", "⚠️ anomaly", "missing_data"]

    def test_save_and_load_report(self):
        """Test saving and loading report."""
        with tempfile.TemporaryDirectory() as tmpdir:
            guardian = GuardianCore()
            guardian.run_all_hooks()

            report_path = Path(tmpdir) / "test_report.json"
            guardian.save_report(str(report_path))

            assert report_path.exists()

            with open(report_path) as f:
                loaded = json.load(f)

            assert "timestamp" in loaded
            assert "hooks" in loaded


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
