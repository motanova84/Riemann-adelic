# QCAL Execution Logs

This directory contains comprehensive execution logs for all tests and validation proofs in the QCAL (Quantum Coherence Adelic Lattice) framework.

## Directory Structure

```
logs/
├── validation/          # Test and validation execution logs
│   ├── *.log           # Detailed text logs with timestamps
│   ├── *.json          # Structured JSON logs for analysis
│   └── pytest_*.log    # Pytest execution logs
├── performance/         # Performance benchmark logs
└── README.md           # This file
```

## Log Types

### 1. Test Session Logs
- **Pattern**: `test_session_YYYYMMDD_HHMMSS.log`
- **Description**: Complete pytest test session logs
- **Format**: Timestamped text with test results
- **JSON**: `test_session_YYYYMMDD_HHMMSS.json` (structured data)

### 2. Individual Test Logs
- **Pattern**: `test_module_test_name_YYYYMMDD_HHMMSS.log`
- **Description**: Detailed logs for individual tests
- **Format**: Timestamped text with checkpoints and metrics
- **JSON**: Includes test metrics, timing, and structured data

### 3. Validation Script Logs
- **Pattern**: `validate_script_name_YYYYMMDD_HHMMSS.log`
- **Description**: Logs from validation and verification scripts
- **Format**: Detailed execution traces with steps
- **JSON**: `validate_script_name_YYYYMMDD_HHMMSS.json`

### 4. Comprehensive Test Run Logs
- **Pattern**: `test_run_summary_YYYYMMDD_HHMMSS.json`
- **Description**: Summary of complete test run with all suites
- **Format**: JSON with status, timing, and results

## Usage

### Running Tests with Logging

#### Using Pytest
```bash
# Run all tests with automatic logging
python -m pytest tests/ -v

# Run specific test with detailed logging
python -m pytest tests/test_coronacion_v5.py -v -s
```

Logs are automatically created in `logs/validation/` directory.

#### Using the qcal_logger Fixture
```python
def test_example(qcal_logger):
    """Example test with QCAL logging."""
    qcal_logger.log_test_start("test_example", "Example test description")
    
    # Log validation steps
    qcal_logger.log_validation_step("Step 1: Setup", 1, 3)
    
    # Log metrics
    qcal_logger.log_metric("accuracy", 0.99, "ratio")
    qcal_logger.log_metric("precision", 30, "decimal places")
    
    # Log checkpoints
    qcal_logger.log_checkpoint("Data loaded successfully")
    
    # Log results
    qcal_logger.log_success("Test completed successfully")
    qcal_logger.log_test_end("test_example", "passed", execution_time=1.234)
```

#### Running Validation Scripts
```bash
# Run V5 Coronación validation with logging
python validate_v5_coronacion.py --verbose --save-certificate

# Run all validations with comprehensive logging
python run_all_tests_with_logs.py --full

# Run quick subset of tests
python run_all_tests_with_logs.py --quick

# Run only pytest tests
python run_all_tests_with_logs.py --pytest-only

# Run only validation scripts
python run_all_tests_with_logs.py --validation-only
```

### Viewing Logs

#### Text Logs
```bash
# View latest test session log
tail -f logs/validation/test_session_*.log

# View specific validation log
cat logs/validation/validate_v5_coronacion_*.log

# Search for errors
grep -r "ERROR" logs/validation/
```

#### JSON Logs
```bash
# Pretty print JSON summary
python -m json.tool logs/validation/test_run_summary_*.json

# Extract specific metrics
jq '.summary' logs/validation/test_session_*.json
```

## Log Contents

### Test Session Log Example
```
================================================================================
QCAL TEST SESSION START
================================================================================
Timestamp: 2025-12-06T23:45:00.000000
Python: 3.12.3
Pytest: 9.0.2
================================================================================

================================================================================
Test: tests/test_coronacion_v5.py::TestCoronacionV5::test_step1_axioms_to_lemmas
Location: tests/test_coronacion_v5.py:34
================================================================================
INFO     | Starting test: test_step1_axioms_to_lemmas
...
SUCCESS  | PASSED: tests/test_coronacion_v5.py::TestCoronacionV5::test_step1_axioms_to_lemmas (1.234s)

================================================================================
QCAL TEST SESSION END
================================================================================
Total tests: 48
Passed: 45
Failed: 2
Skipped: 1
Errors: 0
================================================================================
```

### Validation Script Log Example
```
================================================================================
QCAL VALIDATION EXECUTION LOG
================================================================================
Script: validate_v5_coronacion
Start Time: 2025-12-06T23:45:00.000000
Python: 3.12.3
================================================================================

[2025-12-06 23:45:01] INFO     | Step 1: V5 Coronación Validation
[2025-12-06 23:45:01] INFO     | Precision: 30 decimal places
[2025-12-06 23:45:01] METRIC   | Metric: total_tests = 15
[2025-12-06 23:45:02] SUCCESS  | ✅ SUCCESS: V5 Coronación validation completed successfully

================================================================================
VALIDATION EXECUTION COMPLETE
================================================================================
Script: validate_v5_coronacion
End Time: 2025-12-06T23:45:03.000000
Status: success
================================================================================
```

## Log Rotation and Cleanup

Logs are timestamped and never overwrite existing files. To manage disk space:

```bash
# Delete logs older than 30 days
find logs/validation -name "*.log" -mtime +30 -delete
find logs/validation -name "*.json" -mtime +30 -delete

# Keep only the 100 most recent logs
ls -t logs/validation/*.log | tail -n +101 | xargs rm -f
```

## Integration with CI/CD

The logging system integrates with GitHub Actions workflows:

- Logs are automatically generated during CI runs
- Test artifacts include log files for debugging
- Summary files provide quick status overview

## Mathematical Validation Coherence

All logs maintain QCAL ∞³ coherence standards:

- **Base Frequency**: 141.7001 Hz preserved in all validations
- **QCAL Constant**: C = 244.36 verified in each run
- **Ψ Equation**: Ψ = I × A_eff² × C^∞ maintained
- **DOI References**: All Zenodo DOIs preserved

## Support

For issues with the logging system, please refer to:
- `utils/test_logger.py` - Core logging implementation
- `utils/validation_logger.py` - Validation script logging
- `conftest.py` - Pytest integration

Author: José Manuel Mota Burruezo Ψ ✧ ∞³  
ORCID: 0009-0002-1923-0773  
Instituto de Conciencia Cuántica (ICQ)
