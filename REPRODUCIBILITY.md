# CI/CD Reproducibility Guide

This document describes the reproducibility measures implemented in this repository's CI/CD pipelines.

## Quick Start

### Verify Environment Integrity

```bash
python verify_environment_integrity.py
```

This ensures your environment matches the expected configuration.

### Install Dependencies

```bash
pip install -r requirements-lock.txt
```

### See Also

- [ENV_LOCK_GUIDE.md](ENV_LOCK_GUIDE.md) - Detailed guide on ENV.lock usage
- [SECURITY.md](SECURITY.md) - Security policies including integrity verification

## Overview

To ensure reproducible builds and consistent results across different environments and time periods, this repository implements several key practices:

1. **Pinned Dependencies** - Exact version specifications for all dependencies
2. **Standardized Python Version** - Consistent Python version across all workflows
3. **Pinned Build Tools** - Fixed versions of pip and other build tools
4. **Reproducible Data** - Checksums and versioning for computational data
5. **Environment Integrity** - Automated verification of lock files and checksums

## Dependency Management

### Requirements Files

This repository maintains three related files:

- **`requirements.txt`**: Base requirements with version ranges for development flexibility
- **`requirements-lock.txt`**: Pinned versions for CI/CD reproducibility
- **`ENV.lock`**: Complete environment snapshot generated from requirements-lock.txt

### Environment Integrity Verification

To ensure environment integrity:

```bash
# Verify current environment
python verify_environment_integrity.py

# Generate new checksums after updates
python verify_environment_integrity.py --generate-checksums

# Regenerate ENV.lock from requirements-lock.txt
python generate_env_lock.py
```

### Checksums

All lock files have SHA256 checksums stored in `environment_checksums.json`:

```json
{
  "ENV.lock": "05b062ec...",
  "requirements-lock.txt": "3ed739a3...",
  "requirements.txt": "fb2a8513..."
}
```

These checksums are automatically verified to detect unauthorized modifications.

### Using Requirements-Lock

All CI/CD workflows use `requirements-lock.txt` to ensure reproducible builds:

```bash
python -m pip install --upgrade pip==24.3.1
pip install -r requirements-lock.txt
```

### Updating Dependencies

To update dependencies while maintaining reproducibility:

1. Update `requirements.txt` with new version constraints
2. Create a clean virtual environment:
   ```bash
   python3.11 -m venv venv_clean
   source venv_clean/bin/activate
   ```
3. Install and freeze dependencies:
   ```bash
   pip install --upgrade pip==24.3.1
   pip install -r requirements.txt
   pip freeze > requirements-lock.txt.new
   ```
4. Clean the lock file:
   ```bash
   python clean_requirements_lock.py
   mv requirements-lock.txt.clean requirements-lock.txt
   ```
5. Regenerate ENV.lock and checksums:
   ```bash
   python generate_env_lock.py
   python verify_environment_integrity.py --generate-checksums
   ```
6. Test the changes locally and in CI before merging
7. Commit all updated files:
   ```bash
   git add requirements.txt requirements-lock.txt ENV.lock environment_checksums.json
   git commit -m "Update dependencies: <description>"
   ```

## Python Version Standardization

All workflows use **Python 3.11** for consistency:

```yaml
- name: Set up Python
  uses: actions/setup-python@v5
  with:
    python-version: '3.11'
```

### Why Python 3.11?

- Widely adopted across the project's existing workflows
- Stable and well-supported
- Compatible with all project dependencies
- Balance between new features and stability

## Build Tool Pinning

### Pip Version

All workflows pin pip to version **24.3.1**:

```bash
python -m pip install --upgrade pip==24.3.1
```

This ensures consistent behavior of package installation across runs.

## Dependency Caching

To speed up builds while maintaining reproducibility, this repository uses dependency caching in CI workflows. There are two main approaches:

1. **Built-in pip cache via `setup-python`** (predominant pattern):

   ```yaml
   - name: Set up Python
     uses: actions/setup-python@v5
     with:
       python-version: '3.11'
       cache: 'pip'
The cache key includes:
- Operating system
- Python version
- Hash of requirements-lock.txt

This ensures the cache is invalidated when dependencies change.

## Computational Data Reproducibility

### Riemann Zeros Data

The project uses pre-computed Riemann zeta zeros from Odlyzko's tables:

- Data is fetched from canonical sources
- Checksums validate data integrity
- Version tags (t1e8, t1e10, etc.) ensure consistent datasets

### Validation Parameters

CI workflows use consistent parameters for reproducibility:

```yaml
env:
  PRIME_COUNT: 100
  ZERO_COUNT: 100
  PRIME_POWERS: 3
  INTEGRATION_T: 10
  PRECISION_DPS: 15
```

These are documented in each workflow file and can be overridden for manual runs.

## Workflow Consistency

### Common Patterns

All workflows follow these patterns:

1. **Checkout**: `actions/checkout@v4`
2. **Python Setup**: `actions/setup-python@v5` with version 3.11
3. **Dependency Installation**: Using requirements-lock.txt with pinned pip
4. **Caching**: Using requirements-lock.txt hash in cache keys

### Workflow Types

- **Quick CI** (`quick.yml`): Fast validation on every push
- **Comprehensive CI** (`comprehensive-ci.yml`): Full validation suite
- **Full Validation** (`full.yml`): Manual high-precision runs
- **Specialized Workflows**: Latex, proof checks, etc.

## Artifacts and Retention

Results are stored as artifacts with appropriate retention periods:

- Test results: 30 days
- Validation reports: 30 days
- Consolidated reports: 90 days

## Formal Proof Reproducibility

### Makefile `proof` Target

The repository provides a `proof` Makefile target that builds and verifies all Lean 4 formal content:

```bash
make proof
```

This target:
- Builds all Lean 4 formalization files in `formalization/lean/`
- Verifies type correctness and proof validity
- Uses Lake (Lean's build system) for compilation

### Docker-Based Reproducible Verification

For guaranteed reproducibility across different environments, use the provided Dockerfile:

```bash
# Build the Docker image
docker build -t riemann-adelic-proof .

# Run proof verification in container
docker run --rm riemann-adelic-proof

# Or mount source for development
docker run --rm -v "$PWD":/work -w /work leanprovercommunity/lean:4.5.0 /bin/bash -lc "make proof"
```

**Pinned Versions:**
- Lean 4: `v4.5.0` (specified in `formalization/lean/lean-toolchain`)
- Base Image: `leanprovercommunity/lean:4.5.0`

### Nix Flake for Reproducible Environments

For Nix users, a `flake.nix` is provided for fully reproducible builds:

```bash
# Enter development shell with Lean 4
nix develop

# Build and verify proofs
nix develop --command make proof

# Build as a Nix package
nix build
```

**Pinned Versions in flake.nix:**
- Lean 4: `github:leanprover/lean4/v4.5.0`
- nixpkgs: `nixos-23.11`

### Lake Configuration

The Lean 4 project uses Lake (Lean's build system) with dependencies specified in `formalization/lean/lakefile.lean`:

- **mathlib**: Pinned via git commit in `lake-manifest.json` (auto-generated)
- **Lean version**: Pinned in `formalization/lean/lean-toolchain`

### Reproducibility Guarantees

1. **Version Pinning**: All dependencies (Lean, mathlib) are pinned to specific versions
2. **Containerization**: Docker provides OS-level isolation and reproducibility
3. **Declarative Builds**: Nix flake ensures bit-for-bit reproducible builds
4. **CI Integration**: GitHub Actions workflow (`.github/workflows/lean.yml`) verifies builds

### Manual Verification Steps

To manually verify the formal proofs without Docker/Nix:

1. Install Lean 4 (version 4.5.0):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   elan install leanprover/lean4:v4.5.0
   ```

2. Build the project:
   ```bash
   cd formalization/lean
   lake build
   ```

3. Check specific files:
   ```bash
   lake exe cache get  # Download mathlib cache
   lean --check RiemannAdelic/axioms_to_lemmas.lean
   ```

## Verification

To verify reproducibility:

1. Run the same workflow multiple times
2. Compare output artifacts
3. Verify checksums match
4. Ensure numerical results are within expected precision bounds

## Troubleshooting

### Cache Issues

If cache causes problems:
```bash
# Clear cache manually in GitHub Actions UI
# Or increment cache version in workflow
key: v2-${{ runner.os }}-python-3.11-${{ hashFiles('**/requirements-lock.txt') }}
```

### Dependency Conflicts

If dependencies conflict:
1. Check requirements-lock.txt for version mismatches
2. Recreate the lock file from scratch
3. Test in a clean environment

### Numerical Precision

Mathematical computations may vary slightly due to:
- Floating-point arithmetic differences
- Library implementation changes
- Hardware variations

Expected tolerance levels are documented in test assertions.

## Best Practices

1. **Always use requirements-lock.txt in CI/CD**
2. **Test dependency updates thoroughly**
3. **Document any manual interventions**
4. **Keep lock files up to date with security patches**
5. **Review changes in lock files during code review**

## References

- [pip documentation](https://pip.pypa.io/)
- [GitHub Actions caching](https://docs.github.com/en/actions/using-workflows/caching-dependencies-to-speed-up-workflows)
- [Python version support](https://devguide.python.org/versions/)

## Version History

- **2025-10-18**: Initial implementation
  - Created requirements-lock.txt
  - Standardized Python 3.11 across all workflows
  - Pinned pip to version 24.3.1
  - Updated all workflow caching strategies
