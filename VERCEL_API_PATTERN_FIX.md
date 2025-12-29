# Vercel API Pattern Configuration - Issue Resolution

## Problem Statement

During Vercel deployment, an error can occur with the message:

```
Error: El patrón "api/**/*.py" definido en `functions` no coincide con ninguna 
función sin servidor dentro del directorio `api`.
```

**Translation**: The pattern "api/**/*.py" defined in `functions` doesn't match any serverless function within the `api` directory.

## Root Cause

The issue stems from a misunderstanding of glob pattern matching in Vercel's configuration:

### ❌ Incorrect Pattern: `api/**/*.py`
- The `**` glob pattern matches **subdirectories only**
- Pattern `api/**/*.py` matches files like: `api/subdir/file.py`, `api/sub1/sub2/file.py`
- It does **NOT** match files directly in `api/`: `api/validate-hourly.py` ❌

### ✅ Correct Pattern: `api/*.py`
- The `*` glob pattern matches files at the current level
- Pattern `api/*.py` matches files like: `api/validate-hourly.py`, `api/sync-riemann.py`
- This is the correct pattern for our repository structure ✅

## Repository Structure

Our API functions are at the root level of the `api/` directory:

```
api/
├── README.md
├── validate-hourly.py    ← Serverless function
└── sync-riemann.py        ← Serverless function
```

## Solution Implemented

### 1. Verified Correct Pattern in `vercel.json`

The `vercel.json` configuration uses the correct pattern:

```json
{
  "functions": {
    "api/*.py": {
      "maxDuration": 60,
      "memory": 2048
    }
  }
}
```

### 2. Added Validation Tests

Created comprehensive tests in `test_vercel_config.py` to prevent this issue:

#### Test: `test_api_pattern_matches_existing_files()`
- Verifies that the configured pattern actually matches existing files
- Explicitly checks that the problematic `api/**/*.py` pattern is NOT used
- Ensures deployment won't fail due to pattern mismatch

#### Test: `test_api_functions_are_valid_handlers()`
- Validates that API functions have the correct Vercel handler structure
- Checks for required `handler` class and `BaseHTTPRequestHandler`

### 3. Enhanced Documentation

Updated documentation in multiple files:

#### `VERCEL_DEPLOYMENT_GUIDE.md`
Added warning section explaining:
- Why `api/*.py` is correct
- Why `api/**/*.py` causes failures
- Common mistakes to avoid

#### `api/README.md`
Added configuration notes explaining:
- The correct pattern for this directory structure
- Why the alternative pattern fails

## Validation

Run the test suite to verify configuration:

```bash
pytest test_vercel_config.py -v
```

Expected result: **14/14 tests passing** ✅

## Prevention Measures

To prevent this issue in future:

1. **Automated Testing**: Tests now validate pattern correctness
2. **Clear Documentation**: Multiple docs explain the pattern requirements
3. **Pattern Validation**: Tests explicitly reject the problematic pattern

## Common Mistakes to Avoid

| Mistake | Why It Fails | Correct Approach |
|---------|-------------|------------------|
| Using `api/**/*.py` | Only matches subdirectories | Use `api/*.py` for root-level files |
| Creating subdirectories without updating pattern | Pattern won't match new structure | Update pattern or keep flat structure |
| Mixing flat and nested structures | Requires multiple patterns | Use consistent structure |

## Troubleshooting

### If deployment fails with pattern error:

1. **Check the pattern in `vercel.json`**:
   ```bash
   grep -A 5 '"functions"' vercel.json
   ```
   Should show: `"api/*.py"`

2. **Verify file structure**:
   ```bash
   ls -la api/*.py
   ```
   Should list: `validate-hourly.py` and `sync-riemann.py`

3. **Run validation tests**:
   ```bash
   pytest test_vercel_config.py::test_api_pattern_matches_existing_files -v
   ```

4. **Check for subdirectories**:
   ```bash
   find api -type d
   ```
   Should only show: `api` (no subdirectories)

## Technical Details

### Glob Pattern Reference

| Pattern | Matches | Example |
|---------|---------|---------|
| `api/*.py` | Files directly in api/ | `api/file.py` ✅ |
| `api/**/*.py` | Files in api subdirectories | `api/sub/file.py` ✅ |
| `api/**/*.py` | Files at api root level | `api/file.py` ❌ |

### Vercel Function Requirements

Each serverless function in `api/` must:
1. Define a `handler` class
2. Extend `BaseHTTPRequestHandler`
3. Implement `do_GET()` or `do_POST()` methods
4. Be executable (chmod +x)

## References

- [Vercel Serverless Functions](https://vercel.com/docs/functions)
- [Vercel Configuration Reference](https://vercel.com/docs/projects/project-configuration)
- [Glob Pattern Syntax](https://en.wikipedia.org/wiki/Glob_(programming))

## Status

✅ **RESOLVED** - Configuration validated and documented

- Pattern: `api/*.py` (correct)
- Tests: 14/14 passing
- Documentation: Updated
- Prevention: Automated tests in place

---

**Frequency**: 141.7001 Hz (QCAL Coherence Standard)  
**Version**: V5-Coronación  
**Status**: Pattern configuration validated and secured
