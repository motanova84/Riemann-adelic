# CI/CD Workflow Maintenance Checklist

## Purpose
This checklist ensures that all CI/CD workflows maintain consistency and reproducibility across the repository.

## Before Adding or Modifying Workflows

### 1. Python Version
- [ ] Use Python 3.11 (standardized version across all workflows)
- [ ] Use `actions/setup-python@v5` for Python setup
- [ ] Specify `python-version: '3.11'` explicitly

### 2. Pip Version
- [ ] **ALWAYS** pin pip version: `python -m pip install --upgrade pip==24.3.1`
- [ ] **NEVER** use unpinned: `pip install --upgrade pip` ❌
- [ ] Check all pip install commands in the workflow

### 3. Dependencies
- [ ] Use `requirements-lock.txt` for CI/CD workflows
- [ ] Use `requirements.txt` only for development environments
- [ ] Ensure cache keys use `hashFiles('**/requirements-lock.txt')`

### 4. System Dependencies
For workflows requiring advanced libraries (numba, igraph, etc.):
- [ ] Install LLVM tools: `llvm-14 llvm-14-dev`
- [ ] Install igraph: `libigraph-dev libigraph3t64`
- [ ] Set environment variables:
  ```yaml
  env:
    NUMEXPR_MAX_THREADS: 4
    NUMEXPR_NUM_THREADS: 2
  ```

### 5. Parameter Presets
Use standardized parameter presets from `utils/performance_monitor.py`:

- **quick_test** (for rapid iteration):
  - `max_primes: 50`
  - `max_zeros: 50`
  - `precision_dps: 15`
  - `integration_t: 5`

- **standard_ci** (for CI/CD):
  - `max_primes: 100`
  - `max_zeros: 100`
  - `precision_dps: 25`
  - `integration_t: 10`

- **high_accuracy** (for publication):
  - `max_primes: 500`
  - `max_zeros: 500`
  - `precision_dps: 40`
  - `integration_t: 50`

### 6. Validation Commands
Before committing workflow changes:
```bash
# Check for unpinned pip versions
grep "pip install --upgrade pip[^=]" .github/workflows/*.yml

# Verify all workflows use pip==24.3.1
grep "pip==24.3.1" .github/workflows/*.yml | wc -l

# Check Python version consistency
grep "python-version:" .github/workflows/*.yml | sort | uniq -c
```

## Common Pitfalls to Avoid

### ❌ Don't Do This
```yaml
- name: Install dependencies
  run: |
    pip install --upgrade pip          # Unpinned version!
    pip install numpy scipy            # Not using requirements file!
```

### ✅ Do This Instead
```yaml
- name: Install dependencies
  env:
    NUMEXPR_MAX_THREADS: 4
    NUMEXPR_NUM_THREADS: 2
  run: |
    python -m pip install --upgrade pip==24.3.1
    pip install -r requirements-lock.txt
```

## When to Update Dependencies

### Quarterly Review
- [ ] Review `requirements-lock.txt` for outdated packages
- [ ] Check for security vulnerabilities: `pip-audit`
- [ ] Test with updated dependencies before committing
- [ ] Update `requirements-lock.txt` if needed:
  ```bash
  pip install -r requirements.txt
  pip freeze > requirements-lock.txt
  # Manually clean system-specific packages
  ```

### Security Updates
- [ ] Monitor GitHub Dependabot alerts
- [ ] Update affected packages immediately
- [ ] Regenerate `requirements-lock.txt`
- [ ] Test all workflows after update

## Validation After Changes

### Local Testing
```bash
# Verify pip version installs correctly
python -m pip install --upgrade pip==24.3.1
python -m pip --version  # Should show: pip 24.3.1

# Test dependency installation
pip install -r requirements-lock.txt

# Run validation suite
python validate_v5_coronacion.py --precision 25
pytest tests/ -v
```

### GitHub Actions Testing
- [ ] Create PR with workflow changes
- [ ] Monitor all triggered workflows
- [ ] Check for warnings or errors
- [ ] Verify no "new pip version available" messages

## Documentation Updates

After modifying workflows:
- [ ] Update `CI_CD_REPRODUCIBILITY_SUMMARY.md`
- [ ] Document changes in PR description
- [ ] Update relevant README sections if needed

## Emergency Rollback

If a workflow change breaks CI/CD:
```bash
# Revert to previous working version
git revert <commit-hash>
git push origin <branch>

# Or restore specific workflow file
git checkout HEAD~1 .github/workflows/<workflow-file>.yml
git commit -m "Rollback workflow to previous version"
git push origin <branch>
```

## Version History

- **2025-10-24**: Initial checklist created
- **2025-10-24**: Standardized pip version to 24.3.1 across all workflows

## References

- [CI_CD_REPRODUCIBILITY_SUMMARY.md](./CI_CD_REPRODUCIBILITY_SUMMARY.md)
- [REPRODUCIBILITY.md](./REPRODUCIBILITY.md)
- [requirements-lock.txt](./requirements-lock.txt)
- [utils/performance_monitor.py](./utils/performance_monitor.py)

---

**Important**: Always follow this checklist when creating or modifying CI/CD workflows to maintain consistency and reproducibility across the repository.
