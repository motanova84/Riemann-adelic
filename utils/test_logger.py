"""
QCAL Test Logging System
========================

Comprehensive logging system for all test executions and validations in the QCAL framework.
Provides detailed timestamped logs for mathematical proofs, validations, and test runs.

This module ensures:
- Complete execution logs for each test and proof
- Timestamped log files with rotation
- Structured logging with multiple verbosity levels
- Integration with pytest and validation scripts
- Automatic log archival and cleanup

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import logging
import sys
from datetime import datetime
from pathlib import Path
from typing import Optional, Dict, Any
import json


class QCALTestLogger:
    """
    Unified logging system for QCAL tests and validations.
    
    Features:
    - Automatic log file creation with timestamps
    - Multiple log levels (DEBUG, INFO, WARNING, ERROR, CRITICAL)
    - Structured logging with context information
    - Test execution timing and results tracking
    - Mathematical validation step logging
    - Integration with pytest and standalone scripts
    """
    
    def __init__(
        self,
        name: str,
        log_dir: Optional[Path] = None,
        level: int = logging.INFO,
        console_output: bool = True,
        file_output: bool = True
    ):
        """
        Initialize QCAL test logger.
        
        Args:
            name: Logger name (typically test module or validation script name)
            log_dir: Directory for log files (default: logs/validation/)
            level: Logging level (DEBUG, INFO, WARNING, ERROR, CRITICAL)
            console_output: Whether to output to console
            file_output: Whether to output to log files
        """
        self.name = name
        self.level = level
        self.console_output = console_output
        self.file_output = file_output
        
        # Setup log directory
        if log_dir is None:
            log_dir = Path(__file__).parent.parent / "logs" / "validation"
        self.log_dir = Path(log_dir)
        self.log_dir.mkdir(parents=True, exist_ok=True)
        
        # Create timestamp for this session (with microseconds for uniqueness)
        self.timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
        
        # Setup logger
        self.logger = self._setup_logger()
        
        # Track test execution
        self.test_results: Dict[str, Any] = {
            "timestamp": datetime.now().isoformat(),
            "logger_name": name,
            "tests": [],
            "summary": {
                "passed": 0,
                "failed": 0,
                "skipped": 0,
                "errors": 0
            }
        }
        
    def _setup_logger(self) -> logging.Logger:
        """Setup logger with file and console handlers."""
        logger = logging.getLogger(f"qcal.{self.name}")
        logger.setLevel(self.level)
        logger.handlers.clear()  # Clear any existing handlers
        
        # Create formatters
        detailed_formatter = logging.Formatter(
            '%(asctime)s | %(name)s | %(levelname)-8s | %(message)s',
            datefmt='%Y-%m-%d %H:%M:%S'
        )
        
        console_formatter = logging.Formatter(
            '%(levelname)-8s | %(message)s'
        )
        
        # File handler - detailed logs
        if self.file_output:
            log_file = self.log_dir / f"{self.name}_{self.timestamp}.log"
            file_handler = logging.FileHandler(log_file, encoding='utf-8')
            file_handler.setLevel(logging.DEBUG)
            file_handler.setFormatter(detailed_formatter)
            logger.addHandler(file_handler)
            
            # Also create a JSON log for structured data
            self.json_log_file = self.log_dir / f"{self.name}_{self.timestamp}.json"
        
        # Console handler - user-friendly output
        if self.console_output:
            console_handler = logging.StreamHandler(sys.stdout)
            console_handler.setLevel(self.level)
            console_handler.setFormatter(console_formatter)
            logger.addHandler(console_handler)
        
        return logger
    
    def log_test_start(self, test_name: str, description: str = ""):
        """Log the start of a test."""
        self.logger.info("=" * 80)
        self.logger.info(f"TEST START: {test_name}")
        if description:
            self.logger.info(f"Description: {description}")
        self.logger.info("=" * 80)
        
        self.current_test = {
            "name": test_name,
            "description": description,
            "start_time": datetime.now().isoformat(),
            "status": "running",
            "logs": [],
            "metrics": {}
        }
    
    def log_test_end(self, test_name: str, status: str, error: Optional[str] = None, 
                     execution_time: Optional[float] = None):
        """Log the end of a test with results."""
        self.logger.info("-" * 80)
        self.logger.info(f"TEST END: {test_name}")
        self.logger.info(f"Status: {status}")
        
        if execution_time is not None:
            self.logger.info(f"Execution Time: {execution_time:.3f}s")
        
        if error:
            self.logger.error(f"Error: {error}")
        
        self.logger.info("=" * 80)
        
        # Update test results
        if hasattr(self, 'current_test'):
            self.current_test["end_time"] = datetime.now().isoformat()
            self.current_test["status"] = status
            if error:
                self.current_test["error"] = error
            if execution_time:
                self.current_test["execution_time"] = execution_time
            
            self.test_results["tests"].append(self.current_test.copy())
            
            # Update summary
            if status.lower() == "passed":
                self.test_results["summary"]["passed"] += 1
            elif status.lower() == "failed":
                self.test_results["summary"]["failed"] += 1
            elif status.lower() == "skipped":
                self.test_results["summary"]["skipped"] += 1
            else:
                self.test_results["summary"]["errors"] += 1
    
    def log_validation_step(self, step_name: str, step_number: int, 
                           total_steps: int, theory: str = ""):
        """Log a validation step in mathematical proofs."""
        self.logger.info("")
        self.logger.info(f"📋 Step {step_number}/{total_steps}: {step_name}")
        if theory:
            self.logger.info(f"   Theory: {theory}")
        
        if hasattr(self, 'current_test'):
            self.current_test["logs"].append({
                "type": "validation_step",
                "step": step_number,
                "name": step_name,
                "theory": theory
            })
    
    def log_metric(self, metric_name: str, value: Any, unit: str = ""):
        """Log a metric or measurement."""
        if unit:
            self.logger.info(f"   📊 {metric_name}: {value} {unit}")
        else:
            self.logger.info(f"   📊 {metric_name}: {value}")
        
        if hasattr(self, 'current_test'):
            self.current_test["metrics"][metric_name] = {
                "value": value,
                "unit": unit
            }
    
    def log_checkpoint(self, message: str, data: Optional[Dict] = None):
        """Log a checkpoint with optional structured data."""
        self.logger.info(f"   ✓ {message}")
        
        if hasattr(self, 'current_test'):
            checkpoint = {
                "type": "checkpoint",
                "message": message,
                "timestamp": datetime.now().isoformat()
            }
            if data:
                checkpoint["data"] = data
            self.current_test["logs"].append(checkpoint)
    
    def log_warning(self, message: str):
        """Log a warning."""
        self.logger.warning(f"⚠️  {message}")
    
    def log_error(self, message: str, exception: Optional[Exception] = None):
        """Log an error."""
        self.logger.error(f"❌ {message}")
        if exception:
            self.logger.error(f"   Exception: {type(exception).__name__}: {str(exception)}")
    
    def log_success(self, message: str):
        """Log a success message."""
        self.logger.info(f"✅ {message}")
    
    def debug(self, message: str):
        """Log debug information."""
        self.logger.debug(message)
    
    def info(self, message: str):
        """Log info message."""
        self.logger.info(message)
    
    def save_summary(self):
        """Save test execution summary to JSON file."""
        if self.file_output and hasattr(self, 'json_log_file'):
            self.test_results["end_timestamp"] = datetime.now().isoformat()
            
            with open(self.json_log_file, 'w', encoding='utf-8') as f:
                json.dump(self.test_results, f, indent=2, default=str)
            
            self.logger.info("")
            self.logger.info(f"📝 Test summary saved to: {self.json_log_file}")
    
    def get_summary(self) -> Dict[str, Any]:
        """Get test execution summary."""
        return self.test_results.copy()


def get_test_logger(name: str, **kwargs) -> QCALTestLogger:
    """
    Factory function to get a QCAL test logger.
    
    Args:
        name: Logger name
        **kwargs: Additional arguments passed to QCALTestLogger
    
    Returns:
        QCALTestLogger instance
    """
    return QCALTestLogger(name, **kwargs)
