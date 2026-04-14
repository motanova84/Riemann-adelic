"""
QCAL Validation Script Logger
==============================

Comprehensive logging wrapper for validation and verification scripts.
Automatically logs all validation executions with detailed output.

This module provides:
- Automatic logging for validation scripts
- Detailed execution traces
- Error handling and reporting
- Integration with QCAL logging system
- Output capture and archival

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import sys
import os
from datetime import datetime
from pathlib import Path
from typing import Callable, Any, Dict, Optional
import json
import traceback
import time
from contextlib import contextmanager
import io


class ValidationLogger:
    """
    Logger for validation and verification scripts.
    Captures stdout/stderr and creates comprehensive execution logs.
    """
    
    def __init__(self, script_name: str, log_dir: Optional[Path] = None):
        """
        Initialize validation logger.
        
        Args:
            script_name: Name of the validation script
            log_dir: Directory for log files (default: logs/validation/)
        """
        self.script_name = script_name
        
        # Setup log directory
        if log_dir is None:
            project_root = Path(__file__).parent.parent
            log_dir = project_root / "logs" / "validation"
        self.log_dir = Path(log_dir)
        self.log_dir.mkdir(parents=True, exist_ok=True)
        
        # Create timestamp for this execution
        self.timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        
        # Setup log files
        self.log_file = self.log_dir / f"{script_name}_{self.timestamp}.log"
        self.json_log_file = self.log_dir / f"{script_name}_{self.timestamp}.json"
        
        # Execution data
        self.execution_data = {
            "script_name": script_name,
            "start_time": datetime.now().isoformat(),
            "end_time": None,
            "status": "running",
            "output": [],
            "errors": [],
            "metrics": {},
            "steps": []
        }
        
        # Original stdout/stderr
        self.original_stdout = sys.stdout
        self.original_stderr = sys.stderr
        
        # Open log file
        self.log_handle = open(self.log_file, 'w', encoding='utf-8')
        
        # Write header
        self._write_header()
    
    def _write_header(self):
        """Write log file header."""
        header = f"""
{'=' * 80}
QCAL VALIDATION EXECUTION LOG
{'=' * 80}
Script: {self.script_name}
Start Time: {datetime.now().isoformat()}
Python: {sys.version}
{'=' * 80}

"""
        self.log_handle.write(header)
        self.log_handle.flush()
    
    def _write_footer(self):
        """Write log file footer."""
        footer = f"""
{'=' * 80}
VALIDATION EXECUTION COMPLETE
{'=' * 80}
Script: {self.script_name}
End Time: {datetime.now().isoformat()}
Status: {self.execution_data['status']}
{'=' * 80}
"""
        self.log_handle.write(footer)
        self.log_handle.flush()
    
    def log(self, message: str, level: str = "INFO"):
        """Write a log message."""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        log_line = f"[{timestamp}] {level:8s} | {message}\n"
        self.log_handle.write(log_line)
        self.log_handle.flush()
        
        # Also store in execution data
        self.execution_data["output"].append({
            "timestamp": timestamp,
            "level": level,
            "message": message
        })
    
    def log_step(self, step_name: str, step_number: int = None):
        """Log a validation step."""
        if step_number:
            message = f"Step {step_number}: {step_name}"
        else:
            message = step_name
        
        self.log("=" * 80, "INFO")
        self.log(message, "INFO")
        self.log("=" * 80, "INFO")
        
        self.execution_data["steps"].append({
            "name": step_name,
            "number": step_number,
            "timestamp": datetime.now().isoformat()
        })
    
    def log_metric(self, name: str, value: Any, unit: str = ""):
        """Log a metric."""
        if unit:
            message = f"Metric: {name} = {value} {unit}"
        else:
            message = f"Metric: {name} = {value}"
        
        self.log(message, "METRIC")
        self.execution_data["metrics"][name] = {
            "value": value,
            "unit": unit,
            "timestamp": datetime.now().isoformat()
        }
    
    def log_error(self, error: str, exception: Optional[Exception] = None):
        """Log an error."""
        self.log(f"ERROR: {error}", "ERROR")
        
        error_data = {
            "message": error,
            "timestamp": datetime.now().isoformat()
        }
        
        if exception:
            error_data["exception"] = str(exception)
            error_data["traceback"] = traceback.format_exc()
            self.log(f"Exception: {exception}", "ERROR")
            self.log(f"Traceback:\n{traceback.format_exc()}", "ERROR")
        
        self.execution_data["errors"].append(error_data)
    
    def log_success(self, message: str):
        """Log a success message."""
        self.log(f"✅ SUCCESS: {message}", "SUCCESS")
    
    def log_warning(self, message: str):
        """Log a warning."""
        self.log(f"⚠️  WARNING: {message}", "WARNING")
    
    @contextmanager
    def capture_output(self):
        """
        Context manager to capture stdout and stderr.
        
        Usage:
            with logger.capture_output():
                print("This will be captured")
        """
        # Create string buffers
        stdout_buffer = io.StringIO()
        stderr_buffer = io.StringIO()
        
        # Tee class to write to both original and buffer
        class Tee:
            def __init__(self, original, buffer, log_handle):
                self.original = original
                self.buffer = buffer
                self.log_handle = log_handle
            
            def write(self, data):
                self.original.write(data)
                self.buffer.write(data)
                self.log_handle.write(data)
                self.log_handle.flush()
            
            def flush(self):
                self.original.flush()
                self.buffer.flush()
                self.log_handle.flush()
        
        # Replace stdout and stderr
        sys.stdout = Tee(self.original_stdout, stdout_buffer, self.log_handle)
        sys.stderr = Tee(self.original_stderr, stderr_buffer, self.log_handle)
        
        try:
            yield stdout_buffer, stderr_buffer
        finally:
            # Restore original stdout and stderr
            sys.stdout = self.original_stdout
            sys.stderr = self.original_stderr
    
    def finalize(self, status: str = "completed"):
        """Finalize logging and save summary."""
        self.execution_data["end_time"] = datetime.now().isoformat()
        self.execution_data["status"] = status
        
        # Write footer
        self._write_footer()
        
        # Close log file
        self.log_handle.close()
        
        # Save JSON summary
        with open(self.json_log_file, 'w', encoding='utf-8') as f:
            json.dump(self.execution_data, f, indent=2, default=str)
        
        print(f"\n📝 Validation log saved to: {self.log_file}")
        print(f"📊 Summary saved to: {self.json_log_file}")


def log_validation_execution(script_name: str):
    """
    Decorator to automatically log validation script execution.
    
    Usage:
        @log_validation_execution("validate_riemann_hypothesis")
        def main():
            print("Validating...")
            return True
    """
    def decorator(func: Callable) -> Callable:
        def wrapper(*args, **kwargs):
            logger = ValidationLogger(script_name)
            
            logger.log_step(f"Starting {script_name}", 1)
            logger.log(f"Function: {func.__name__}", "INFO")
            
            start_time = time.time()
            result = None
            status = "completed"
            
            try:
                with logger.capture_output():
                    result = func(*args, **kwargs)
                
                logger.log_success(f"{script_name} completed successfully")
                
            except Exception as e:
                status = "failed"
                logger.log_error(f"Execution failed: {str(e)}", e)
                raise
            
            finally:
                execution_time = time.time() - start_time
                logger.log_metric("execution_time", execution_time, "seconds")
                logger.finalize(status)
            
            return result
        
        return wrapper
    return decorator


def run_with_logging(script_name: str, func: Callable, *args, **kwargs) -> Any:
    """
    Run a function with comprehensive logging.
    
    Args:
        script_name: Name for the log files
        func: Function to execute
        *args, **kwargs: Arguments to pass to the function
    
    Returns:
        Function result
    """
    logger = ValidationLogger(script_name)
    
    logger.log_step(f"Executing {script_name}", 1)
    
    start_time = time.time()
    result = None
    status = "completed"
    
    try:
        with logger.capture_output():
            result = func(*args, **kwargs)
        
        logger.log_success(f"{script_name} completed successfully")
        
    except Exception as e:
        status = "failed"
        logger.log_error(f"Execution failed: {str(e)}", e)
        raise
    
    finally:
        execution_time = time.time() - start_time
        logger.log_metric("execution_time", execution_time, "seconds")
        logger.finalize(status)
    
    return result
