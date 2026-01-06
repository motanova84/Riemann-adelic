# ENV.lock Usage Guide

## Overview

The `ENV.lock` file provides a comprehensive snapshot of the Python environment used for QCAL validation and Riemann Hypothesis proof verification. It ensures **complete reproducibility** across different machines, time periods, and execution environments.

## Purpose

- **Reproducibility**: Ensures that validation results can be reproduced exactly
- **Integrity**: Provides checksums for verifying file integrity
- **Documentation**: Records the exact environment used for proof verification
- **Auditability**: Creates an audit trail for scientific reproducibility

## File Structure

```
ENV.lock
├── Header (comments with metadata)
├── Package list (alphabetically sorted)
│   ├── package-name==version
│   └── ...
└── 70 packages total (as of latest version)
```

## Relationship with requirements-lock.txt

| File | Purpose | Usage |
|------|---------|-------|
| `requirements.txt` | Development dependencies with version ranges | Local development |
| `requirements-lock.txt` | Pinned CI/CD dependencies | CI/CD pipelines |
| `ENV.lock` | Complete environment snapshot | Reproducibility verification |

**Key Difference**: `ENV.lock` is generated FROM `requirements-lock.txt` and includes all specified packages in a normalized format.

## Generating ENV.lock

### Automatic Generation

```bash
python generate_env_lock.py
```

This creates `ENV.lock` from `requirements-lock.txt` with:
- Header comments with generation metadata
- Alphabetically sorted package list
- Clean formatting

### Manual Generation (from current environment)

```bash
python generate_env_lock.py --from-freeze
```

This uses `pip freeze` to capture the actual installed environment.

⚠️ **Warning**: Only use `--from-freeze` when you want to snapshot the current environment. The canonical source is `requirements-lock.txt`.

## Verifying Environment Integrity

### Quick Verification

```bash
python verify_environment_integrity.py
```

This checks:
- ✅ ENV.lock and requirements-lock.txt exist
- ✅ Files are consistent with each other
- ✅ Checksums match expected values
- ⚠️ Installed packages match lock files (warning only)
- ⚠️ Python version matches expected version

### Generate New Checksums

```bash
python verify_environment_integrity.py --generate-checksums
```

Use this when:
- Creating a new ENV.lock file
- Updating dependencies intentionally
- Setting up a new environment

### Verbose Output

```bash
python verify_environment_integrity.py --verbose
```

Shows detailed information about:
- Each verification step
- Package counts
- Checksum generation

## Checksums and Integrity

### Checksum File

`environment_checksums.json` contains SHA256 checksums for:
- `ENV.lock`
- `requirements-lock.txt`
- `requirements.txt`

Example:
```json
{
  "ENV.lock": "05b062ecdaf8902a185b8daacfd275d882004dd7007b49719f6460c76203912b",
  "requirements-lock.txt": "3ed739a34dcb62d4f46e58e54357a2fb49411e9276a9deccc40d50d89147227c",
  "requirements.txt": "fb2a851332642187855bc93488ca8719ef6da0e8214513c78b6b6380c734a9bc"
}
```

### Verifying Checksums

The verification script automatically checks that current files match saved checksums:

```bash
python verify_environment_integrity.py
```

If checksums don't match:
```
❌ Checksum mismatches detected: ENV.lock, requirements-lock.txt.
   Lock files may have been modified.
```

## CI/CD Integration

### Workflow Integration

Add to `.github/workflows/*.yml`:

```yaml
- name: Verify environment integrity
  run: |
    python verify_environment_integrity.py
```

This ensures:
- Lock files haven't been corrupted
- Dependencies are consistent
- Environment is reproducible

### Pre-commit Hook

Add to `.pre-commit-config.yaml`:

```yaml
- repo: local
  hooks:
    - id: verify-env-integrity
      name: Verify environment integrity
      entry: python verify_environment_integrity.py
      language: system
      pass_filenames: false
      always_run: true
```

## Updating Dependencies

### Workflow

1. **Update requirements.txt** with new version constraints:
   ```bash
   # Edit requirements.txt
   vim requirements.txt
   ```

2. **Clean install in fresh environment**:
   ```bash
   python3.11 -m venv venv_clean
   source venv_clean/bin/activate
   pip install --upgrade pip==24.3.1
   pip install -r requirements.txt
   ```

3. **Generate new lock file**:
   ```bash
   pip freeze > requirements-lock.txt.new
   python clean_requirements_lock.py
   mv requirements-lock.txt.clean requirements-lock.txt
   ```

4. **Regenerate ENV.lock**:
   ```bash
   python generate_env_lock.py
   ```

5. **Update checksums**:
   ```bash
   python verify_environment_integrity.py --generate-checksums
   ```

6. **Test thoroughly**:
   ```bash
   pytest tests/
   python validate_v5_coronacion.py
   ```

7. **Commit all changes**:
   ```bash
   git add ENV.lock requirements-lock.txt environment_checksums.json
   git commit -m "Update dependencies: <description>"
   ```

## Troubleshooting

### Version Mismatches

**Problem**: Verification shows version mismatches between lock files.

**Solution**: Regenerate ENV.lock from requirements-lock.txt:
```bash
python generate_env_lock.py
python verify_environment_integrity.py --generate-checksums
```

### Checksum Failures

**Problem**: Checksums don't match.

**Solution**: 
1. Check if files were modified:
   ```bash
   git diff ENV.lock requirements-lock.txt
   ```

2. If changes are intentional, regenerate checksums:
   ```bash
   python verify_environment_integrity.py --generate-checksums
   ```

3. If changes are NOT intentional, revert:
   ```bash
   git checkout ENV.lock requirements-lock.txt
   ```

### Python Version Warnings

**Problem**: Python version mismatch warning.

**Context**: The project specifies Python 3.11 for reproducibility.

**Solutions**:
- Install Python 3.11 using pyenv:
  ```bash
  pyenv install 3.11
  pyenv local 3.11
  ```
- Use Docker with Python 3.11
- Results may still work but reproducibility is not guaranteed

### Missing Packages

**Problem**: Packages not installed warning.

**Solution**: Install from requirements-lock.txt:
```bash
pip install -r requirements-lock.txt
```

## Best Practices

### ✅ Do

- ✅ Always use `requirements-lock.txt` in CI/CD
- ✅ Verify integrity before important validations
- ✅ Regenerate checksums after intentional changes
- ✅ Keep ENV.lock synchronized with requirements-lock.txt
- ✅ Document reasons for dependency updates

### ❌ Don't

- ❌ Manually edit ENV.lock
- ❌ Skip integrity verification in CI/CD
- ❌ Mix packages from different Python versions
- ❌ Update dependencies without testing
- ❌ Commit lock files without checksums

## Scientific Reproducibility

### Why It Matters

The Riemann Hypothesis proof requires:
- **Numerical precision**: Exact library versions affect precision
- **Algorithmic stability**: Different versions may have different algorithms
- **Result verification**: Independent verification requires identical environments

### Verification Process

1. **Environment Setup**: Install exact versions from ENV.lock
2. **Integrity Check**: Verify checksums match
3. **Validation Run**: Execute validation scripts
4. **Result Comparison**: Compare with published results

### Publishing Results

When publishing validation results:
1. Include ENV.lock checksum in paper
2. Reference specific ENV.lock version
3. Provide ENV.lock in supplementary materials
4. Document Python version and OS

## References

- **REPRODUCIBILITY.md**: Overall reproducibility guidelines
- **SECURITY.md**: Security policies
- **requirements-lock.txt**: CI/CD dependencies
- **verify_environment_integrity.py**: Verification script
- **generate_env_lock.py**: Generation script

## Version History

- **2026-01-06**: Initial version
  - Created ENV.lock from requirements-lock.txt
  - Added checksum verification
  - Implemented automated generation

## Support

For questions or issues:
- Open a GitHub issue
- Check REPRODUCIBILITY.md
- Contact: institutoconsciencia@proton.me

---

**Last Updated**: 2026-01-06  
**Maintained by**: José Manuel Mota Burruezo  
**License**: MIT
