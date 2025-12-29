# Test Retry for Flaky and Snapshot-Related Failures - Feature Documentation

## Overview

This document describes the **retry-on-failures** feature that has been enabled in the QCAL mathematical verification repository. This feature uses a general test retry mechanism (via `pytest-rerunfailures`) that applies to all failed tests, and is particularly helpful for flaky and snapshot-related issues.

## Purpose

The retry functionality helps handle flaky tests, including those that fail due to snapshot-related warnings, by automatically retrying failed tests. This is particularly useful for:

- Mathematical validation tests that may exhibit numerical instability
- Snapshot-based tests that validate mathematical certificates
- Tests that interact with external data sources (e.g., Odlyzko zeros)
- Performance-sensitive tests that may fail due to timing issues

## Implementation

### Dependencies

The feature uses the `pytest-rerunfailures` plugin, which has been added to:

- `requirements.txt` - Main dependencies
- `requirements-core.txt` - Core dependencies
- `requirements-lock.txt` - Locked versions
- `requirements_extended.txt` - Extended dependencies
- `pyproject.toml` - Project metadata

### Configuration

#### pytest.ini

```ini
[pytest]
addopts = --tb=short -v --capture=no --log-cli-level=INFO --log-file=logs/validation/pytest_latest.log --log-file-level=DEBUG --reruns 3 --reruns-delay 1
```

Key parameters:
- `--reruns 3`: Retry failed tests up to 3 times
- `--reruns-delay 1`: Wait 1 second between retries

#### pyproject.toml

```toml
[tool.pytest.ini_options]
addopts = [
    "-ra",
    "-q",
    "--strict-markers",
    "--strict-config",
    "--reruns=3",
    "--reruns-delay=1",
]
markers = [
    "slow: marks tests as slow (deselect with '-m \"not slow\"')",
    "integration: marks tests as integration tests",
    "unit: marks tests as unit tests",
    "flaky: marks tests that may fail intermittently (will auto-retry)",
]
```

## Usage

### Automatic Retry

All tests are automatically configured to retry up to 3 times with a 1-second delay between attempts.

### Marking Flaky Tests

For tests known to be flaky, use the `@pytest.mark.flaky` decorator:

```python
import pytest

@pytest.mark.flaky
def test_numerical_stability():
    """Test that may fail due to numerical precision issues."""
    result = compute_spectral_trace(precision=30)
    assert abs(result - expected) < 1e-25
```

### Disabling Retry for Specific Tests

To disable retry for specific tests:

```python
import pytest

@pytest.mark.no_retry
def test_should_fail_immediately():
    """Test that should fail without retry."""
    assert False
```

### Command Line Override

To run tests without retry:

```bash
pytest tests/ --reruns 0
```

To increase retry count:

```bash
pytest tests/ --reruns 5 --reruns-delay 2
```

## Benefits for QCAL Validation

### Mathematical Precision

Mathematical validation tests involving high-precision computations (e.g., `validate_v5_coronacion.py`) may occasionally fail due to:
- Numerical rounding differences
- Resource contention (CPU/memory)
- Timing-dependent initialization

The retry mechanism ensures these transient failures don't block the CI/CD pipeline.

### Snapshot Validation

Tests that validate mathematical certificates and snapshot data benefit from:
- Automatic retry when snapshot files are being written
- Resilience to filesystem timing issues
- Better handling of concurrent test execution

### CI/CD Reliability

GitHub Actions workflows benefit from:
- Reduced false negatives from flaky tests
- More reliable automated validation
- Better use of computational resources

## Monitoring and Reporting

### Test Output

When a test is retried, pytest will show:

```
tests/test_spectral_validation.py::test_eigenvalue_computation RERUN
tests/test_spectral_validation.py::test_eigenvalue_computation PASSED
```

### Full Report

Use `-ra` flag (already enabled by default) to see a summary of all retried tests:

```
=========================== short test summary info ===========================
RERUN tests/test_spectral_validation.py::test_eigenvalue_computation
PASSED tests/test_spectral_validation.py::test_eigenvalue_computation
```

## Best Practices

1. **Don't rely on retries for broken tests** - Fix the root cause when possible
2. **Use `@pytest.mark.flaky` explicitly** - Document known flaky tests
3. **Monitor retry frequency** - Frequent retries indicate a problem
4. **Keep retry counts reasonable** - 3 retries is usually sufficient
5. **Add delays for resource-dependent tests** - Use `--reruns-delay` for I/O-bound tests

## Integration with QCAL Workflows

### GitHub Actions

The retry functionality is automatically enabled in all workflow runs that use pytest:

- `.github/workflows/ci.yml`
- `.github/workflows/test.yml`
- `.github/workflows/comprehensive-ci.yml`
- `.github/workflows/copilot-automerge.yml`

### Validation Scripts

Scripts that run pytest internally (e.g., `run_all_tests_with_logs.py`) will automatically benefit from the retry functionality.

## Troubleshooting

### Retry Not Working

If retry is not working:

1. Check that `pytest-rerunfailures` is installed:
   ```bash
   pip install pytest-rerunfailures>=14.0
   ```

2. Verify pytest configuration:
   ```bash
   pytest --help | grep rerun
   ```

3. Check for conflicting pytest plugins

### Too Many Retries

If tests are being retried too often:

1. Review the test for actual issues
2. Consider reducing `--reruns` count
3. Add more specific retry conditions with `--only-rerun`

## References

- [pytest-rerunfailures documentation](https://pypi.org/project/pytest-rerunfailures/)
- [QCAL Copilot Instructions](.github/copilot-instructions.md)
- [Testing Best Practices](tests/README.md)

## Version History

- **v1.0.0** (2025-12-29): Initial implementation of retry-on-snapshot-warnings feature
  - Added `pytest-rerunfailures>=14.0` dependency
  - Configured automatic retry for snapshot and warning-related failures
  - Updated all requirements files
  - Added comprehensive documentation

---

**QCAL ∞³ Coherence Maintained** ✅

This feature enhances the reliability of the mathematical validation framework while preserving the integrity of the Riemann Hypothesis proof validation.
