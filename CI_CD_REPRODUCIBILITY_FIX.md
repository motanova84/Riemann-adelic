# CI/CD Reproducibility Fix Summary

## Issue Description
The CI/CD pipeline was failing due to dependency version conflicts and Python version inconsistencies across workflows.

### Root Cause
1. **Missing requirements-lock.txt**: The error log showed an attempt to install from `requirements-lock.txt` with pinned versions, but this file didn't exist.
2. **Invalid qiskit version**: The locked requirements tried to install `qiskit==1.3.4`, which doesn't exist (latest 1.3.x is 1.3.3).
3. **Inconsistent Python versions**: Workflows used Python 3.10, 3.11, and 3.12 inconsistently, leading to dependency compatibility issues.

## Changes Made

### 1. Created requirements-lock.txt
- Added `requirements-lock.txt` with pinned, Python 3.11-compatible versions
- Fixed qiskit version to 1.3.3 (the actual latest 1.3.x release)
- Pinned top-level dependencies to specific versions for reproducibility:
  - mpmath==1.3.0
  - numpy==1.26.4
  - scipy==1.16.2
  - sympy==1.12
  - matplotlib==3.10.0
  - qiskit==1.3.3
  - And all other dependencies

### 2. Standardized Python Version to 3.11
Updated all workflows to use Python 3.11:
- `.github/workflows/critical-line-verification.yml`
- `.github/workflows/full.yml`
- `.github/workflows/quick.yml`
- `.github/workflows/v5-coronacion-proof-check.yml`
- `.github/workflows/advanced-validation.yml`
- `.github/workflows/status.yml`
- `.github/workflows/performance-benchmark.yml`

### 3. Updated Documentation
- Updated README.md to specify Python 3.11 as the recommended version
- Added instructions for reproducible installation using `requirements-lock.txt`
- Documented the difference between `requirements.txt` (flexible) and `requirements-lock.txt` (pinned)

## Usage

### For Development (flexible versions)
```bash
pip install -r requirements.txt
```

### For CI/CD or Reproducible Builds (pinned versions)
```bash
pip install -r requirements-lock.txt
```

## Benefits
1. **Reproducibility**: Exact same dependency versions across all environments
2. **Compatibility**: All packages verified to work with Python 3.11
3. **Reliability**: No more version conflicts or missing packages
4. **Consistency**: Single Python version across all CI/CD workflows

## Testing
To verify the fix works:
```bash
# Create a clean environment
python3.11 -m venv test-env
source test-env/bin/activate

# Install pinned dependencies
pip install --upgrade pip==24.3.1
pip install -r requirements-lock.txt

# Run tests
pytest tests/
```

## Related Issues
- Issue #2161: Fix CI/CD reproducibility problems
- PR #438: Solucione los problemas de reproducibilidad de CI/CD

## Version Information
- Python: 3.11 (standardized across all workflows)
- pip: 24.3.1+ (recommended)
- All dependencies: See requirements-lock.txt for exact versions
