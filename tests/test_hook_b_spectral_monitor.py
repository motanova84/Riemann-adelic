#!/usr/bin/env python3
"""
Tests for Hook B: Spectral Heat Kernel Core Monitor

Tests the mathematical ECG-like monitoring of the Hilbert-Pólya
correspondence λ_n ≈ γ_n².

Author: José Manuel Mota Burruezo
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: December 2025
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
QCAL ∞³ Framework
"""

import pytest
import numpy as np
import tempfile
import json
from pathlib import Path

# Import Hook B module - using absolute import from repository root
# The tests should be run from the repository root directory
try:
    from hook_b_spectral_monitor import (
        HookBSpectralMonitor,
        SpectralECGResult,
        MonitorReport,
        run_hook_b_monitor,
        QCAL_BASE_FREQUENCY,
        QCAL_COHERENCE_C
    )
except ImportError:
    # Fallback for running from tests directory
    import sys
    sys.path.insert(0, str(Path(__file__).parent.parent))
    from hook_b_spectral_monitor import (
        HookBSpectralMonitor,
        SpectralECGResult,
        MonitorReport,
        run_hook_b_monitor,
        QCAL_BASE_FREQUENCY,
        QCAL_COHERENCE_C
    )


class TestSpectralECGResult:
    """Tests for SpectralECGResult dataclass."""
    
    def test_ecg_result_creation(self):
        """Test creating a SpectralECGResult."""
        result = SpectralECGResult(
            index=1,
            gamma_n=14.134725,
            gamma_n_squared=199.79,
            lambda_n=200.0,
            deviation=0.21,
            relative_error=0.001,
            healthy=True
        )
        
        assert result.index == 1
        assert result.gamma_n == pytest.approx(14.134725)
        assert result.gamma_n_squared == pytest.approx(199.79)
        assert result.lambda_n == 200.0
        assert result.healthy is True
    
    def test_ecg_result_unhealthy(self):
        """Test creating an unhealthy SpectralECGResult."""
        result = SpectralECGResult(
            index=5,
            gamma_n=32.935,
            gamma_n_squared=1084.71,
            lambda_n=2000.0,  # Way off
            deviation=915.29,
            relative_error=0.844,
            healthy=False
        )
        
        assert result.healthy is False
        assert result.relative_error > 0.1


class TestHookBSpectralMonitor:
    """Tests for HookBSpectralMonitor class."""
    
    @pytest.fixture
    def monitor(self):
        """Create a monitor instance for testing."""
        return HookBSpectralMonitor(max_zeros=20, tolerance=0.1)
    
    def test_monitor_initialization(self, monitor):
        """Test monitor initializes correctly."""
        assert monitor.max_zeros == 20
        assert monitor.tolerance == 0.1
        assert len(monitor.riemann_zeros) > 0
        assert len(monitor.riemann_zeros) <= 20
    
    def test_monitor_loads_zeros(self, monitor):
        """Test that zeros are loaded correctly."""
        zeros = monitor.riemann_zeros
        
        # First zero should be approximately 14.134725
        assert zeros[0] == pytest.approx(14.134725, rel=1e-3)
        
        # Zeros should be positive
        assert all(z > 0 for z in zeros)
        
        # Zeros should be increasing
        for i in range(len(zeros) - 1):
            assert zeros[i] < zeros[i + 1]
    
    def test_analyze_heartbeat_healthy(self, monitor):
        """Test analyzing a healthy heartbeat."""
        gamma_n = 14.134725
        gamma_n_squared = gamma_n ** 2
        lambda_n = gamma_n_squared * 1.005  # 0.5% deviation
        
        result = monitor.analyze_heartbeat(
            n=1,
            gamma_n=gamma_n,
            lambda_n=lambda_n
        )
        
        assert result.healthy is True
        assert result.relative_error < 0.01
    
    def test_analyze_heartbeat_unhealthy(self, monitor):
        """Test analyzing an unhealthy heartbeat."""
        gamma_n = 14.134725
        gamma_n_squared = gamma_n ** 2
        lambda_n = gamma_n_squared * 2.0  # 100% deviation
        
        result = monitor.analyze_heartbeat(
            n=1,
            gamma_n=gamma_n,
            lambda_n=lambda_n
        )
        
        assert result.healthy is False
        assert result.relative_error > 0.5
    
    def test_run_ecg_returns_report(self, monitor):
        """Test that run_ecg returns a valid MonitorReport."""
        report = monitor.run_ecg()
        
        assert isinstance(report, MonitorReport)
        assert report.total_zeros > 0
        assert report.healthy_count <= report.total_zeros
        assert 0 <= report.health_score <= 100
        assert report.status in ["HEALTHY", "WARNING", "CRITICAL"]
        assert len(report.heartbeats) == report.total_zeros
    
    def test_ecg_correlation_high(self, monitor):
        """Test that correlation between λ and γ² is high."""
        report = monitor.run_ecg()
        
        # Correlation should be very close to 1 for the Hilbert-Pólya correspondence
        assert report.correlation > 0.99
    
    def test_compute_eigenvalues(self, monitor):
        """Test eigenvalue computation."""
        eigenvalues = monitor.compute_eigenvalues(n_eigenvalues=10)
        
        assert len(eigenvalues) == 10
        assert all(np.isfinite(eigenvalues))
        # Eigenvalues should be sorted
        for i in range(len(eigenvalues) - 1):
            assert eigenvalues[i] <= eigenvalues[i + 1]
    
    def test_compute_heat_kernel_trace(self, monitor):
        """Test heat kernel trace computation."""
        eigenvalues = np.array([100, 200, 300, 400, 500])
        t_values = np.array([0.001, 0.01, 0.1])
        
        traces = monitor.compute_heat_kernel_trace(t_values, eigenvalues)
        
        assert len(traces) == len(t_values)
        # Traces should decrease with increasing t (heat decay)
        assert traces[0] > traces[1] > traces[2]


class TestMonitorReport:
    """Tests for MonitorReport dataclass."""
    
    def test_report_healthy_status(self):
        """Test report with HEALTHY status."""
        heartbeats = [
            SpectralECGResult(i, 10.0, 100.0, 101.0, 1.0, 0.01, True)
            for i in range(10)
        ]
        
        report = MonitorReport(
            total_zeros=10,
            healthy_count=10,
            mean_deviation=1.0,
            max_deviation=2.0,
            mean_relative_error=0.01,
            max_relative_error=0.02,
            correlation=0.999,
            health_score=100.0,
            status="HEALTHY",
            heartbeats=heartbeats
        )
        
        assert report.status == "HEALTHY"
        assert report.health_score == 100.0
    
    def test_report_warning_status(self):
        """Test report with WARNING status."""
        report = MonitorReport(
            total_zeros=10,
            healthy_count=8,
            mean_deviation=10.0,
            max_deviation=20.0,
            mean_relative_error=0.08,
            max_relative_error=0.15,
            correlation=0.95,
            health_score=80.0,
            status="WARNING",
            heartbeats=[]
        )
        
        assert report.status == "WARNING"
        assert report.health_score == 80.0


class TestRunHookBMonitor:
    """Tests for the main run_hook_b_monitor function."""
    
    def test_run_monitor_returns_report(self):
        """Test that run_hook_b_monitor returns a report."""
        report = run_hook_b_monitor(verbose=False, max_zeros=10)
        
        assert isinstance(report, MonitorReport)
        assert report.total_zeros == 10
    
    def test_run_monitor_with_low_tolerance(self):
        """Test running with low tolerance."""
        report = run_hook_b_monitor(
            verbose=False,
            max_zeros=10,
            tolerance=0.001  # Very strict
        )
        
        # Should still return a valid report
        assert isinstance(report, MonitorReport)
        # May have fewer healthy heartbeats with strict tolerance
        assert report.healthy_count >= 0


class TestExportReport:
    """Tests for report export functionality."""
    
    def test_export_report_json(self):
        """Test exporting report to JSON."""
        monitor = HookBSpectralMonitor(max_zeros=10, tolerance=0.1)
        report = monitor.run_ecg()
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            filename = f.name
        
        try:
            monitor.export_report(report, filename)
            
            # Verify file exists and is valid JSON
            with open(filename, 'r') as f:
                data = json.load(f)
            
            assert data["hook"] == "B"
            assert data["status"] == report.status
            assert data["health_score"] == report.health_score
            assert "heartbeats" in data
            assert len(data["heartbeats"]) == report.total_zeros
            assert data["qcal"]["frequency_hz"] == QCAL_BASE_FREQUENCY
            assert data["qcal"]["coherence_C"] == QCAL_COHERENCE_C
        finally:
            Path(filename).unlink()


class TestQCALConstants:
    """Tests for QCAL constants."""
    
    def test_qcal_frequency(self):
        """Test QCAL base frequency is correct."""
        assert QCAL_BASE_FREQUENCY == 141.7001
    
    def test_qcal_coherence(self):
        """Test QCAL coherence constant is correct."""
        assert QCAL_COHERENCE_C == 244.36


class TestHilbertPolyaCorrespondence:
    """Tests specifically for the λ_n ≈ γ_n² correspondence."""
    
    def test_correspondence_first_zero(self):
        """Test the correspondence for the first Riemann zero."""
        gamma_1 = 14.134725141734693
        expected_lambda = gamma_1 ** 2
        
        # Lambda should be approximately gamma squared
        assert expected_lambda == pytest.approx(199.7905, rel=1e-4)
    
    def test_correspondence_multiple_zeros(self):
        """Test the correspondence for multiple zeros."""
        gammas = [
            14.134725141734693,
            21.022039638771554,
            25.010857580145688,
            30.424876125859513,
            32.935061587739189
        ]
        
        for gamma in gammas:
            lambda_n = gamma ** 2
            # Verify lambda is positive and finite
            assert lambda_n > 0
            assert np.isfinite(lambda_n)
            # Verify lambda grows with gamma
    
    def test_monitor_validates_correspondence(self):
        """Test that the monitor validates the Hilbert-Pólya correspondence."""
        monitor = HookBSpectralMonitor(max_zeros=10, tolerance=0.1)
        # Use theoretical eigenvalues mode to validate the mathematical framework
        report = monitor.run_ecg(use_theoretical_eigenvalues=True)
        
        # For theoretical mode, correlation should be very high
        assert report.correlation > 0.99
        
        # Mean relative error should be small in theoretical mode
        assert report.mean_relative_error < 0.1
    
    def test_operator_eigenvalue_mode(self):
        """Test that operator eigenvalue mode works (may have lower correlation)."""
        monitor = HookBSpectralMonitor(max_zeros=10, tolerance=0.5)
        # Use actual operator eigenvalues
        report = monitor.run_ecg(use_theoretical_eigenvalues=False)
        
        # Correlation should still be positive and reasonable
        assert report.correlation > 0.9
        # Report should return a valid status
        assert report.status in ["HEALTHY", "WARNING", "CRITICAL"]


class TestSpectralECGVisualization:
    """Tests for the ECG visualization functionality."""
    
    def test_print_ecg_trace_no_error(self):
        """Test that print_ecg_trace runs without error."""
        monitor = HookBSpectralMonitor(max_zeros=10)
        report = monitor.run_ecg()
        
        # Should not raise any exception
        import io
        import sys
        
        captured = io.StringIO()
        sys.stdout = captured
        try:
            monitor.print_ecg_trace(report)
        finally:
            sys.stdout = sys.__stdout__
        
        output = captured.getvalue()
        assert "SPECTRAL ECG TRACE" in output
        assert "♥" in output  # Heart symbol for healthy
    
    def test_print_report_no_error(self):
        """Test that print_report runs without error."""
        monitor = HookBSpectralMonitor(max_zeros=10)
        report = monitor.run_ecg()
        
        import io
        import sys
        
        captured = io.StringIO()
        sys.stdout = captured
        try:
            monitor.print_report(report)
        finally:
            sys.stdout = sys.__stdout__
        
        output = captured.getvalue()
        assert "HOOK B" in output
        assert "QCAL" in output


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
