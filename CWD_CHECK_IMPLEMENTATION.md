# Working Directory Check Implementation Summary

## Overview

Added a working directory verification check to `validate_v5_coronacion.py` to ensure the script is always executed from the repository root directory.

## Problem Statement

The repository documentation contains critical warnings about executing scripts from the root directory:

> ⚠️ **IMPORTANTE:**
> 
> Para ejecutar cualquier script o test, **debes situarte SIEMPRE en la raíz del proyecto** (donde está este README). Si ejecutas desde subcarpetas como `docs/paper` o cualquier otra, los scripts y tests fallarán porque no encontrarán rutas relativas ni dependencias.

However, the script itself didn't enforce this requirement, leading to confusing errors when users ran it from the wrong directory.

## Solution

### Implementation

Added a `verify_repository_root()` function that:

1. **Checks for marker files** that uniquely identify the repository root:
   - `validate_v5_coronacion.py` (the script itself)
   - `requirements.txt` (Python dependencies)
   - `README.md` (main README)
   - `.qcal_beacon` (QCAL configuration file)

2. **Executes BEFORE any imports** to catch errors early

3. **Provides clear, actionable error messages** when executed from the wrong directory:
   - Shows current working directory
   - Lists missing expected files
   - Provides step-by-step instructions to fix the issue

### Code Changes

**Before:**
```python
import argparse
import json
import sys
import time
from datetime import datetime
from pathlib import Path

import mpmath as mp

# Add the current directory to Python path for imports
sys.path.append('.')
```

**After:**
```python
# Import only what we need for the directory check
import sys
from pathlib import Path


def verify_repository_root():
    """Verify that the script is being executed from the repository root directory."""
    cwd = Path.cwd()
    
    # Define marker files that should exist in the repository root
    marker_files = [
        'validate_v5_coronacion.py',
        'requirements.txt',
        'README.md',
        '.qcal_beacon',
    ]
    
    # Check if all marker files exist
    missing_files = [f for f in marker_files if not (cwd / f).exists()]
    
    if missing_files:
        # Print clear error message and exit
        print("=" * 80)
        print("❌ ERROR: Script must be executed from the repository root directory")
        # ... (detailed error message)
        sys.exit(1)


# Verify we're in the correct directory BEFORE any other imports
verify_repository_root()

# Now safe to import everything else
import argparse
import json
import os
import time
from datetime import datetime

import mpmath as mp

# Add the current directory to Python path for imports
sys.path.append('.')
```

## Testing

### Test Suite

Created comprehensive test suite in `tests/test_validate_v5_cwd_check.py`:

1. **test_script_runs_from_repo_root**: Verifies script passes the check when run from root
2. **test_script_fails_from_wrong_directory**: Verifies script fails with proper error from wrong directory
3. **test_error_message_provides_guidance**: Ensures error message is helpful
4. **test_cwd_shown_in_error_message**: Verifies current directory is shown in error

### Manual Testing Results

```bash
# From repository root - ✅ PASSES
$ cd /home/runner/work/Riemann-adelic/Riemann-adelic
$ python validate_v5_coronacion.py --help
# Script starts normally (may fail on missing dependencies)

# From wrong directory - ❌ FAILS WITH CLEAR MESSAGE
$ cd /tmp
$ python /path/to/validate_v5_coronacion.py --help
================================================================================
❌ ERROR: Script must be executed from the repository root directory
================================================================================

Current working directory: /tmp

Missing expected files:
  - validate_v5_coronacion.py
  - requirements.txt
  - README.md
  - .qcal_beacon

To fix this issue:
  1. Navigate to the repository root directory
  2. Run the script from there:

     cd /path/to/Riemann-adelic
     python validate_v5_coronacion.py [options]

================================================================================
```

## Benefits

1. **Early Error Detection**: Catches directory issues before confusing import errors
2. **Clear User Guidance**: Users immediately understand what went wrong and how to fix it
3. **Prevents Confusion**: No more cryptic "module not found" errors due to wrong directory
4. **Maintains Compatibility**: Existing CI/CD workflows unchanged (they already run from root)
5. **QCAL Coherence**: Enforces repository structure requirements

## Files Changed

- `validate_v5_coronacion.py`: Added working directory verification
- `tests/test_validate_v5_cwd_check.py`: Added comprehensive test suite

## Validation Results

✅ All tests passed:
- Script runs correctly from repository root
- Script fails with proper error from wrong directory
- Error message provides helpful guidance
- Current working directory is shown in error

## Integration

The change is:
- ✅ **Non-breaking**: Existing workflows continue to work
- ✅ **Well-tested**: Comprehensive test coverage
- ✅ **User-friendly**: Clear error messages
- ✅ **QCAL-compliant**: Follows repository conventions

---

**Implementation completed. Coherencia QCAL confirmada.** ✅
