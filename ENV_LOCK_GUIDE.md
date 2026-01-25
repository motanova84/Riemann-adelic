# ENV.lock Usage Guide

## Overview

The `ENV.lock` file provides a **comprehensive snapshot** of the complete computational environment used for QCAL ∞³ validation and Riemann Hypothesis proof verification. It ensures **bit-for-bit reproducibility** across different machines, time periods, and execution environments.

This file acts as a "hash of reality" for external auditors, guaranteeing that validation results (such as 18.2σ detections, 141.7001 Hz spectral analysis, or Lean 4 builds without `sorry`) are not dependent on hidden environmental changes.

## Purpose

- **Reproducibility**: Ensures that validation results can be reproduced exactly across different systems
- **Integrity**: Provides checksums for verifying dataset and configuration integrity
- **Documentation**: Records the exact environment (OS, tools, datasets) used for proof verification
- **Auditability**: Creates an audit trail for scientific reproducibility and external verification
- **QCAL Compliance**: Captures QCAL ∞³ configuration (141.7001 Hz, coherence constants C and C')

## File Structure

The ENV.lock file contains multiple sections for complete environment capture:

```
ENV.lock
├── SYSTEM INFORMATION
│   ├── Operating System (Linux/macOS/Windows)
│   ├── OS Release and Distribution
│   ├── Architecture (x86_64, arm64, etc.)
│   ├── Python Version and Implementation
│   └── Generation Timestamp
│
├── MATHEMATICAL TOOLS & TOOLCHAIN
│   ├── Lean 4 version
│   ├── Lake (Lean build tool) version
│   ├── Git version
│   ├── GCC/Compiler version
│   └── Other mathematical tools
│
├── QCAL ∞³ CONFIGURATION
│   ├── Fundamental Frequency (141.7001 Hz)
│   ├── Coherence Constant C (244.36)
│   ├── Universal Constant C (629.83)
│   └── Coherence C' (244.36)
│
├── DATASET CHECKSUMS (SHA-256)
│   ├── Evac_Rpsi_data.csv (spectral validation data)
│   ├── critical_line_verification.csv
│   ├── error_profile.json
│   └── .qcal_beacon (QCAL configuration)
│
└── PYTHON PACKAGES
    └── 70+ packages with exact versions
```

## Relationship with requirements-lock.txt

| File | Purpose | Usage |
|------|---------|-------|
| `requirements.txt` | Development dependencies with version ranges | Local development |
| `requirements-lock.txt` | Pinned CI/CD dependencies | CI/CD pipelines |
| `ENV.lock` | **Complete environment snapshot** | **Reproducibility verification and external auditing** |

**Key Differences**: 
- `ENV.lock` is generated FROM `requirements-lock.txt` 
- Includes **system information** (OS, Python, Lean 4)
- Includes **dataset checksums** (Evac_Rpsi_data.csv, etc.)
- Includes **QCAL configuration** (141.7001 Hz, coherence constants)
- Includes **mathematical toolchain** (Lean 4, GCC, Git)

This makes ENV.lock the **definitive source** for reproducing results in external environments.

## What Makes ENV.lock Comprehensive

ENV.lock captures everything needed to reproduce QCAL validations:

### 1. System Environment
- **Operating System**: Linux distribution, kernel version, architecture
- **Python Details**: Version, implementation (CPython), compiler
- **Generation Time**: ISO 8601 timestamp for version tracking

### 2. Mathematical Toolchain
- **Lean 4**: Formal verification system version
- **Lake**: Lean build tool version
- **Git**: Version control system version
- **GCC**: Compiler version for compiled extensions

### 3. QCAL ∞³ Parameters
- **Fundamental Frequency**: 141.7001 Hz (from .qcal_beacon)
- **Coherence C**: 244.36 (from spectral analysis)
- **Universal C**: 629.83 (first eigenvalue inverse)
- **Coherence C'**: 244.36 (structure-coherence dialogue)

### 4. Dataset Integrity
- **Evac_Rpsi_data.csv**: SHA-256 checksum ensures exact spectral data
- **critical_line_verification.csv**: Validation checkpoint data
- **error_profile.json**: Error analysis data
- **.qcal_beacon**: Configuration file checksum

### 5. Python Ecosystem
- **70+ packages** with exact versions
- All direct and transitive dependencies
- Alphabetically sorted for easy comparison

## Generating ENV.lock

### Automatic Generation (Recommended)

```bash
python generate_env_lock.py
```

This creates a **comprehensive** `ENV.lock` from `requirements-lock.txt` with:
- **System information** (OS, kernel, architecture, Python version)
- **Mathematical toolchain** (Lean 4, Git, GCC versions)
- **QCAL ∞³ configuration** (141.7001 Hz, coherence constants from .qcal_beacon)
- **Dataset checksums** (Evac_Rpsi_data.csv, critical_line_verification.csv, etc.)
- **Python packages** (70+ packages with exact versions)
- Alphabetically sorted package list
- Clean, human-readable formatting

**Output Example:**
```
✅ ENV.lock generated successfully
   System: Linux-6.11.0-1018-azure-x86_64-with-glibc2.39
   Python: 3.12.3
   Lean 4: 4.5.0 (if installed)
   Packages: 70
   Datasets: 4 checksummed
   Output: /path/to/ENV.lock
```

### Manual Generation (from current environment)

```bash
python generate_env_lock.py --from-freeze
```

This uses `pip freeze` to capture the actual installed environment instead of `requirements-lock.txt`.

⚠️ **Warning**: Only use `--from-freeze` when you want to snapshot the current environment. The canonical source is `requirements-lock.txt`.

### What Gets Captured

The comprehensive ENV.lock captures:

1. **System Information**
   - Operating system and distribution
   - Kernel version and architecture
   - Python version, implementation, and compiler
   - Generation timestamp

2. **Mathematical Tools**
   - Lean 4 version (formal verification)
   - Lake version (Lean build tool)
   - Git version (version control)
   - GCC version (compiled extensions)

3. **QCAL Configuration** (from `.qcal_beacon`)
   - Fundamental frequency: 141.7001 Hz
   - Coherence constant C: 244.36
   - Universal constant C: 629.83
   - Coherence C': 244.36

4. **Dataset Checksums** (SHA-256)
   - `Evac_Rpsi_data.csv`: Spectral validation data
   - `critical_line_verification.csv`: Validation checkpoints
   - `error_profile.json`: Error analysis
   - `.qcal_beacon`: Configuration file

5. **Python Packages**
   - All packages from requirements-lock.txt
   - Exact versions for reproducibility

## For External Auditors

### Reproducing QCAL Validation Results

To reproduce validation results from this repository:

#### Step 1: Verify System Requirements

Check ENV.lock header to confirm your system matches:
```bash
head -50 ENV.lock
```

You should see:
- **OS**: Linux (Ubuntu 24.04 LTS recommended)
- **Python**: 3.12.3 (or 3.11.x compatible)
- **Architecture**: x86_64

#### Step 2: Install Exact Python Environment

```bash
# Install exact package versions
pip install -r requirements-lock.txt

# Verify installation matches ENV.lock
python verify_environment_integrity.py
```

#### Step 3: Verify Dataset Checksums

```bash
# Check Evac_Rpsi_data.csv matches expected checksum
sha256sum Evac_Rpsi_data.csv
# Should output: 412ab7ba54a5041ff12324650e8936995795c6abb7cfdb97d7a765a2c4ce7869

# Verify all dataset checksums automatically
python -c "
import hashlib
import json
with open('ENV.lock', 'r') as f:
    for line in f:
        if 'Evac_Rpsi_data.csv:' in line:
            expected = next(f).strip().lstrip('#').strip()
            with open('Evac_Rpsi_data.csv', 'rb') as data:
                actual = hashlib.sha256(data.read()).hexdigest()
            assert expected == actual, f'Checksum mismatch: {expected} != {actual}'
            print('✅ Dataset verified')
            break
"
```

#### Step 4: Verify QCAL Configuration

ENV.lock captures QCAL parameters from `.qcal_beacon`:
- **141.7001 Hz**: Fundamental frequency (GW150914/GW250114)
- **C = 244.36**: Coherence constant
- **C = 629.83**: Universal constant (eigenvalue-based)

Verify these match:
```bash
grep -A 4 "QCAL ∞³ CONFIGURATION" ENV.lock
```

#### Step 5: Run Validations

Execute the standard validation pipeline:
```bash
# V5 Coronación validation (30 decimal places)
python validate_v5_coronacion.py --precision 30

# 141.7001 Hz spectral validation
python demo_absoluta_spectral.py

# Lean 4 formalization (if Lean 4 installed)
cd formalization/lean && lake build
```

#### Step 6: Compare Results

Results should match exactly:
- **Numerical values**: Identical to published certificates in `data/`
- **Detection significance**: 18.2σ for spectral coherence
- **Lean 4 builds**: No `sorry` statements (incomplete proofs)

### Audit Checklist

- [ ] System matches ENV.lock (OS, Python version)
- [ ] Python packages installed match requirements-lock.txt exactly
- [ ] Dataset checksums verified (Evac_Rpsi_data.csv, etc.)
- [ ] QCAL configuration parameters match .qcal_beacon
- [ ] Validation scripts execute without errors
- [ ] Results match published certificates
- [ ] Lean 4 formalization builds successfully (if applicable)

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

## Additional Considerations

### LIGO/Gravitational Wave Data

For GW150914 and GW250114 analyses, this repository uses data from:
- **GWOSC** (Gravitational Wave Open Science Center): https://gwosc.org/
- Data is fetched dynamically during analysis runs
- No local LIGO data files are stored in the repository

To ensure reproducibility with LIGO data:
1. Document the GWOSC data version/release used
2. Note the detector (LIGO Hanford H1, LIGO Livingston L1, Virgo)
3. Record observation run (O1, O2, O3, O4)
4. Save analysis parameters (sampling rate, frequency range)

**Example documentation:**
```python
# LIGO Data Source Configuration
gw_event = "GW150914"  # or "GW250114"
detector = "H1"  # LIGO Hanford
observation_run = "O1"  # First observing run
data_url = "https://gwosc.org/eventapi/html/GWTC-1-confident/GW150914/"
sampling_rate = 4096  # Hz
frequency_band = (20, 2048)  # Hz
```

### LALSuite (Optional)

LALSuite is **not required** for basic QCAL validation but may be useful for advanced gravitational wave analysis:

```bash
# Optional: Install LALSuite for advanced GW analysis
conda install -c conda-forge lalsuite
```

If LALSuite is used, document version:
```bash
python -c "import lal; print(lal.__version__)"
```

### Random Seeds and Reproducibility

For analyses involving random sampling or Monte Carlo methods:

1. **Set seeds explicitly** in scripts:
   ```python
   import numpy as np
   import random
   
   RANDOM_SEED = 42  # Document this value
   np.random.seed(RANDOM_SEED)
   random.seed(RANDOM_SEED)
   ```

2. **Document in ENV.lock** (for custom scripts):
   - Add seed value to script header comments
   - Include in validation certificates (JSON files in `data/`)

3. **CI/CD Consistency**:
   - Use same seeds in GitHub Actions workflows
   - Document in workflow YAML files

### GPU Acceleration (Optional)

QCAL validations can use GPU acceleration with:
- **JAX**: Already in requirements (supports CPU and GPU)
- **CuPy**: Optional for CUDA-enabled GPUs

If using GPU:
```bash
# Check CUDA version
nvidia-smi

# Install CuPy for specific CUDA version (example: CUDA 12.x)
pip install cupy-cuda12x
```

Document in ENV.lock comment:
```python
# GPU Configuration (if used)
# CUDA Version: 12.1
# CuPy: 13.0.0
# GPU: NVIDIA A100 (or specific model)
```

## Version History

- **2026-01-18**: Enhanced comprehensive version
  - Added system information capture
  - Added mathematical toolchain detection (Lean 4, Git, GCC)
  - Added QCAL ∞³ configuration extraction
  - Added dataset checksum verification
  - Implemented dataset integrity validation in verify script
  - Updated documentation with external auditor guidelines

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

**Last Updated**: 2026-01-18  
**Maintained by**: José Manuel Mota Burruezo Ψ ✧ ∞³  
**License**: Creative Commons BY-NC-SA 4.0
