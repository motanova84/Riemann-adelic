# QCAL Comprehensive Execution Logging System

## Overview

The QCAL framework now includes a comprehensive logging system that automatically captures detailed execution logs for all tests and validation proofs. Every test run, validation script, and mathematical proof verification is logged with timestamps, metrics, and structured data.

## Features

✨ **Automatic Test Logging**: All pytest tests automatically generate detailed logs  
📊 **Structured Data**: JSON logs for easy analysis and programmatic access  
⏱️ **Timing Information**: Execution time tracking for performance monitoring  
📝 **Validation Steps**: Mathematical proof steps logged with theory references  
🔍 **Error Tracking**: Comprehensive error messages and stack traces  
📈 **Metrics Capture**: Numerical metrics and measurements recorded  
🎯 **QCAL Coherence**: Maintains QCAL ∞³ standards and references  

## Quick Start

### Running Tests with Automatic Logging

```bash
# Run all tests with automatic logging
python -m pytest tests/ -v

# Run specific test file
python -m pytest tests/test_coronacion_v5.py -v

# Run single test with detailed output
python -m pytest tests/test_coronacion_v5.py::TestCoronacionV5::test_step1_axioms_to_lemmas -v -s
```

All logs are automatically saved to `logs/validation/` directory.

### Running Validation Scripts

```bash
# Run V5 Coronación validation
python validate_v5_coronacion.py --verbose

# Run with custom precision
python validate_v5_coronacion.py --precision 50 --max_zeros 100

# Save mathematical proof certificate
python validate_v5_coronacion.py --save-certificate
```

### Comprehensive Test Runner

Run all tests and validations with a single command:

```bash
# Run all tests and validations
python run_all_tests_with_logs.py --full

# Quick subset (recommended for development)
python run_all_tests_with_logs.py --quick

# Only pytest tests
python run_all_tests_with_logs.py --pytest-only

# Only validation scripts
python run_all_tests_with_logs.py --validation-only
```

## Using the QCAL Logger in Tests

### Basic Usage

```python
def test_example(qcal_logger):
    """Example test with QCAL logging."""
    qcal_logger.log_test_start("test_example", "Example test description")
    
    # Your test code here
    result = perform_calculation()
    
    qcal_logger.log_success("Calculation completed")
    qcal_logger.log_test_end("test_example", "passed")
```

### Logging Validation Steps

```python
def test_riemann_hypothesis_proof(qcal_logger):
    """Test RH proof with detailed step logging."""
    qcal_logger.log_test_start(
        "test_riemann_hypothesis_proof",
        "Complete RH proof validation"
    )
    
    # Step 1
    qcal_logger.log_validation_step(
        "Axioms → Lemmas",
        step_number=1,
        total_steps=5,
        theory="Adelic theory (Tate, Weil)"
    )
    validate_step1()
    qcal_logger.log_checkpoint("Step 1 verified")
    
    # Step 2
    qcal_logger.log_validation_step(
        "Archimedean Rigidity",
        step_number=2,
        total_steps=5,
        theory="Weil index + stationary phase"
    )
    validate_step2()
    qcal_logger.log_checkpoint("Step 2 verified")
    
    qcal_logger.log_test_end("test_riemann_hypothesis_proof", "passed")
```

### Logging Metrics

```python
def test_numerical_accuracy(qcal_logger):
    """Test with numerical metrics logging."""
    qcal_logger.log_test_start("test_numerical_accuracy", "Accuracy validation")
    
    error = calculate_error()
    precision = 30
    
    # Log metrics
    qcal_logger.log_metric("relative_error", error, "")
    qcal_logger.log_metric("precision", precision, "decimal places")
    qcal_logger.log_metric("frequency", 141.7001, "Hz")
    qcal_logger.log_metric("coherence", 244.36, "")
    
    if error < 1e-10:
        qcal_logger.log_success("Accuracy requirement met")
    else:
        qcal_logger.log_warning(f"Error too high: {error}")
    
    qcal_logger.log_test_end("test_numerical_accuracy", "passed")
```

### Logging Checkpoints and Warnings

```python
def test_with_checkpoints(qcal_logger):
    """Test with multiple checkpoints."""
    qcal_logger.log_test_start("test_with_checkpoints", "Checkpoint example")
    
    # Checkpoint with message only
    qcal_logger.log_checkpoint("Data loaded successfully")
    
    # Checkpoint with structured data
    qcal_logger.log_checkpoint("Validation complete", {
        "zeros_checked": 100,
        "all_on_critical_line": True
    })
    
    # Warning
    qcal_logger.log_warning("Some non-critical issue detected")
    
    # Debug information
    qcal_logger.debug("Internal state: processing batch 5")
    
    qcal_logger.log_test_end("test_with_checkpoints", "passed")
```

## Creating Validation Scripts with Logging

### Using the Decorator

```python
from utils.validation_logger import log_validation_execution

@log_validation_execution("my_validation")
def validate_theorem():
    """Validate a mathematical theorem."""
    print("Starting validation...")
    
    # Perform validation
    result = verify_theorem()
    
    print(f"Validation result: {result}")
    return result

if __name__ == '__main__':
    validate_theorem()
```

### Manual Logging

```python
from utils.validation_logger import ValidationLogger

def main():
    """Main validation function."""
    logger = ValidationLogger("custom_validation")
    
    logger.log_step("Starting custom validation", 1)
    logger.log("Initializing parameters")
    
    try:
        # Step 1
        logger.log_step("Computing eigenvalues", 2)
        eigenvalues = compute_eigenvalues()
        logger.log_metric("eigenvalue_count", len(eigenvalues))
        logger.log_success("Eigenvalues computed")
        
        # Step 2
        logger.log_step("Verifying critical line", 3)
        all_on_line = verify_critical_line(eigenvalues)
        logger.log_metric("critical_line_verified", all_on_line)
        
        if all_on_line:
            logger.log_success("All zeros on critical line")
            logger.finalize("success")
        else:
            logger.log_error("Some zeros off critical line")
            logger.finalize("failed")
            
    except Exception as e:
        logger.log_error("Validation failed", e)
        logger.finalize("error")

if __name__ == '__main__':
    main()
```

## Log File Locations

All logs are stored in the `logs/validation/` directory:

```
logs/validation/
├── test_session_YYYYMMDD_HHMMSS.log        # Pytest session log
├── test_session_YYYYMMDD_HHMMSS.json       # Pytest session JSON
├── validate_script_YYYYMMDD_HHMMSS.log     # Validation script log
├── validate_script_YYYYMMDD_HHMMSS.json    # Validation script JSON
├── test_run_summary_YYYYMMDD_HHMMSS.json   # Comprehensive test run summary
└── pytest_latest.log                        # Latest pytest run (symlink)
```

## Log Formats

### Text Log Format

```
================================================================================
QCAL VALIDATION EXECUTION LOG
================================================================================
Script: validate_v5_coronacion
Start Time: 2025-12-06T23:48:33.263673
Python: 3.12.3
================================================================================

[2025-12-06 23:48:33] INFO     | Step 1: V5 Coronación Validation
[2025-12-06 23:48:33] INFO     | Precision: 30 decimal places
[2025-12-06 23:48:35] METRIC   | Metric: total_tests = 15
[2025-12-06 23:48:35] SUCCESS  | ✅ SUCCESS: Validation completed

================================================================================
VALIDATION EXECUTION COMPLETE
================================================================================
```

### JSON Log Format

```json
{
  "script_name": "validate_v5_coronacion",
  "start_time": "2025-12-06T23:48:33.263608",
  "end_time": "2025-12-06T23:48:35.645544",
  "status": "success",
  "metrics": {
    "total_tests": {"value": 15, "unit": "", "timestamp": "..."},
    "passed_tests": {"value": 12, "unit": "", "timestamp": "..."}
  },
  "steps": [
    {"name": "V5 Coronación Validation", "number": 1, "timestamp": "..."}
  ],
  "errors": []
}
```

## Viewing and Analyzing Logs

### View Latest Logs

```bash
# View latest test session log
tail -f logs/validation/test_session_*.log

# View latest validation log
tail -f logs/validation/validate_v5_coronacion_*.log
```

### Search Logs

```bash
# Find all errors
grep -r "ERROR" logs/validation/

# Find specific test results
grep "test_step1_axioms_to_lemmas" logs/validation/*.log

# Find all successful validations
grep "SUCCESS" logs/validation/*.log
```

### Analyze JSON Logs

```bash
# Pretty print JSON
python -m json.tool logs/validation/test_session_*.json

# Extract summary
jq '.summary' logs/validation/test_session_*.json

# Extract metrics
jq '.metrics' logs/validation/validate_v5_coronacion_*.json

# Find failed tests
jq '.tests[] | select(.outcome == "failed")' logs/validation/*.json
```

## Log Management

### Automatic Cleanup

The logging system creates timestamped files that never overwrite existing logs. To manage disk space:

```bash
# Delete logs older than 30 days
find logs/validation -name "*.log" -mtime +30 -delete
find logs/validation -name "*.json" -mtime +30 -delete

# Keep only the 100 most recent logs
ls -t logs/validation/*.log | tail -n +101 | xargs rm -f
ls -t logs/validation/*.json | tail -n +101 | xargs rm -f
```

### Archiving Logs

```bash
# Create archive of all logs
tar -czf logs_archive_$(date +%Y%m%d).tar.gz logs/validation/

# Archive and remove old logs
tar -czf logs_archive.tar.gz logs/validation/*.log logs/validation/*.json
find logs/validation -name "*.log" -mtime +7 -delete
find logs/validation -name "*.json" -mtime +7 -delete
```

## CI/CD Integration

The logging system integrates seamlessly with GitHub Actions:

```yaml
# .github/workflows/tests.yml
- name: Run tests with logging
  run: |
    python run_all_tests_with_logs.py --full

- name: Upload logs
  if: always()
  uses: actions/upload-artifact@v3
  with:
    name: test-logs
    path: logs/validation/
```

## QCAL Coherence Standards

All logs maintain QCAL ∞³ coherence:

- ✅ **Base Frequency**: 141.7001 Hz preserved in validations
- ✅ **QCAL Constant**: C = 244.36 verified
- ✅ **Ψ Equation**: Ψ = I × A_eff² × C^∞ maintained
- ✅ **DOI References**: All Zenodo DOIs preserved
- ✅ **Mathematical Rigor**: All proofs logged with theory references

## Troubleshooting

### Logs Not Being Created

Check that the logs directory exists:
```bash
mkdir -p logs/validation
```

### Permission Issues

Ensure write permissions:
```bash
chmod -R u+w logs/
```

### Import Errors

Ensure the utils module is in the Python path:
```python
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
```

## Examples

See `logs/README.md` for detailed examples of log formats and usage patterns.

## Support

For issues or questions:
- Check `utils/test_logger.py` for core logging implementation
- Check `utils/validation_logger.py` for validation script logging
- Check `conftest.py` for pytest integration

---

**Author**: José Manuel Mota Burruezo Ψ ✧ ∞³  
**ORCID**: 0009-0002-1923-0773  
**Institution**: Instituto de Conciencia Cuántica (ICQ)  
**Framework**: QCAL ∞³ (Quantum Coherence Adelic Lattice)
