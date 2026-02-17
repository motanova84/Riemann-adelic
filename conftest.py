"""
QCAL Pytest Configuration and Logging Hooks
============================================

Pytest configuration file that provides comprehensive logging for all tests.
Automatically captures test execution details, timing, and results.

This configuration:
- Automatically logs all test executions with timestamps
- Captures stdout/stderr for each test
- Generates detailed test reports
- Integrates with QCAL logging system
- Creates per-test-session summaries

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""
import sys
import os
import pytest
import logging
from datetime import datetime
from pathlib import Path
import json
from typing import Dict, List, Any

# Add the project root directory to Python path so we can import from utils
project_root = os.path.dirname(os.path.abspath(__file__))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

from utils.test_logger import QCALTestLogger


# Global test session logger
_session_logger = None
_test_loggers: Dict[str, QCALTestLogger] = {}
_session_results: Dict[str, Any] = {
    "start_time": None,
    "end_time": None,
    "tests": [],
    "summary": {
        "passed": 0,
        "failed": 0,
        "skipped": 0,
        "error": 0,
        "total": 0
    }
}


def pytest_configure(config):
    """Configure pytest with QCAL logging system."""
    global _session_logger
    
    # Create session logger
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    _session_logger = QCALTestLogger(
        name=f"test_session_{timestamp}",
        log_dir=Path(__file__).parent / "logs" / "validation",
        level=logging.INFO,
        console_output=False,  # Don't duplicate pytest output
        file_output=True
    )
    
    _session_logger.info("=" * 80)
    _session_logger.info("QCAL TEST SESSION START")
    _session_logger.info(f"Timestamp: {datetime.now().isoformat()}")
    _session_logger.info(f"Python: {sys.version}")
    _session_logger.info(f"Pytest: {pytest.__version__}")
    _session_logger.info("=" * 80)
    
    _session_results["start_time"] = datetime.now().isoformat()


def pytest_unconfigure(config):
    """Cleanup and save session summary."""
    global _session_logger, _session_results
    
    if _session_logger:
        _session_results["end_time"] = datetime.now().isoformat()
        
        _session_logger.info("=" * 80)
        _session_logger.info("QCAL TEST SESSION END")
        _session_logger.info(f"Total tests: {_session_results['summary']['total']}")
        _session_logger.info(f"Passed: {_session_results['summary']['passed']}")
        _session_logger.info(f"Failed: {_session_results['summary']['failed']}")
        _session_logger.info(f"Skipped: {_session_results['summary']['skipped']}")
        _session_logger.info(f"Errors: {_session_results['summary']['error']}")
        _session_logger.info("=" * 80)
        
        # Save session summary
        _session_logger.test_results = _session_results
        _session_logger.save_summary()


def pytest_runtest_logstart(nodeid, location):
    """Called at the start of running a test."""
    global _session_logger
    
    if _session_logger:
        _session_logger.info("")
        _session_logger.info("=" * 80)
        _session_logger.info(f"Test: {nodeid}")
        _session_logger.info(f"Location: {location[0]}:{location[1]}")
        _session_logger.info("=" * 80)


def pytest_runtest_logreport(report):
    """Process test report and log results."""
    global _session_logger, _session_results
    
    if report.when == "call":  # Only log the actual test call, not setup/teardown
        _session_results["summary"]["total"] += 1
        
        test_info = {
            "nodeid": report.nodeid,
            "outcome": report.outcome,
            "duration": report.duration,
            "timestamp": datetime.now().isoformat()
        }
        
        if report.outcome == "passed":
            _session_results["summary"]["passed"] += 1
            if _session_logger:
                _session_logger.log_success(f"PASSED: {report.nodeid} ({report.duration:.3f}s)")
        
        elif report.outcome == "failed":
            _session_results["summary"]["failed"] += 1
            if _session_logger:
                _session_logger.log_error(f"FAILED: {report.nodeid} ({report.duration:.3f}s)")
                if hasattr(report, 'longrepr'):
                    _session_logger.info(str(report.longrepr))
            test_info["error"] = str(report.longrepr) if hasattr(report, 'longrepr') else ""
        
        elif report.outcome == "skipped":
            _session_results["summary"]["skipped"] += 1
            if _session_logger:
                _session_logger.log_warning(f"SKIPPED: {report.nodeid}")
        
        _session_results["tests"].append(test_info)


@pytest.fixture(scope="function")
def qcal_logger(request):
    """
    Pytest fixture providing a QCAL logger for individual tests.
    
    Usage in tests:
        def test_example(qcal_logger):
            qcal_logger.log_test_start("test_example", "Example test")
            qcal_logger.log_checkpoint("Step 1 complete")
            qcal_logger.log_metric("accuracy", 0.99, "ratio")
            qcal_logger.log_test_end("test_example", "passed")
    """
    global _test_loggers
    
    # Create logger for this test
    test_name = request.node.name
    module_name = request.node.module.__name__ if hasattr(request.node, 'module') else "unknown"
    
    logger_name = f"{module_name}.{test_name}"
    
    if logger_name not in _test_loggers:
        logger = QCALTestLogger(
            name=logger_name.replace(".", "_"),
            log_dir=Path(__file__).parent / "logs" / "validation",
            level=logging.DEBUG,
            console_output=False,
            file_output=True
        )
        _test_loggers[logger_name] = logger
    
    logger = _test_loggers[logger_name]
    logger.log_test_start(test_name, f"Test from {module_name}")
    
    yield logger
    
    # Test ended
    outcome = "unknown"
    if hasattr(request.node, 'rep_call'):
        if request.node.rep_call.passed:
            outcome = "passed"
        elif request.node.rep_call.failed:
            outcome = "failed"
        elif request.node.rep_call.skipped:
            outcome = "skipped"
    
    logger.log_test_end(test_name, outcome)
    logger.save_summary()


@pytest.hookimpl(tryfirst=True, hookwrapper=True)
def pytest_runtest_makereport(item, call):
    """
    Hook to make test report available to fixtures.
    Allows fixtures to access test outcomes.
    """
    outcome = yield
    rep = outcome.get_result()
    setattr(item, f"rep_{rep.when}", rep)


@pytest.fixture(scope="session")
def session_logger():
    """Provide access to the session-level logger."""
    return _session_logger