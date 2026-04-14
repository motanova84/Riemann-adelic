# ENV.lock Quick Start for External Auditors

## What is ENV.lock?

**ENV.lock** is a comprehensive "hash of reality" for the QCAL ∞³ ecosystem. It captures **everything** needed to reproduce validation results bit-for-bit across any system.

## Why It Matters

For auditors verifying:
- **141.7001 Hz detections** (GW150914/GW250114 gravitational waves)
- **Riemann Hypothesis proof** (V5 Coronación validation)
- **Birch-Swinnerton-Dyer** validations
- **P vs NP** spectral connections

ENV.lock ensures results are **independent of hidden environmental changes**.

## What's Captured

✅ **System Environment**
- OS, kernel, architecture (Ubuntu 24.04 LTS, x86_64)
- Python 3.12.3 (CPython, GCC 13.3.0)

✅ **Mathematical Tools**
- Lean 4, Git, GCC versions
- SAT solvers (if applicable)

✅ **QCAL ∞³ Configuration**
- Frequency: **141.7001 Hz**
- Coherence C (spectral moment): **244.36**
- Universal C (eigenvalue): **629.83**

✅ **Dataset Integrity** (SHA-256 checksums)
- `Evac_Rpsi_data.csv`: Spectral validation data
- `critical_line_verification.csv`: Validation checkpoints
- `error_profile.json`: Error analysis
- `.qcal_beacon`: QCAL configuration

✅ **Python Packages**
- 70+ packages with exact versions
- NumPy, SciPy, JAX, Qiskit, etc.

## Quick Verification (3 Commands)

### 1. Install Exact Environment

```bash
pip install -r requirements-lock.txt
```

### 2. Verify Integrity

```bash
python verify_environment_integrity.py --verbose
```

**Expected output:**
```
✅ Lock files consistency check: 70 packages verified
✅ Dataset checksums verified: 4 files
✅ All checksums verified successfully
✅ Verification PASSED
```

### 3. Run Validations

```bash
# V5 Coronación (Riemann Hypothesis)
python validate_v5_coronacion.py --precision 30

# 141.7001 Hz spectral analysis
python demo_absoluta_spectral.py

# Lean 4 formalization (if Lean 4 installed)
cd formalization/lean && lake build
```

## Reproducing Results

### Step-by-Step Audit

1. **Clone repository**
   ```bash
   git clone https://github.com/motanova84/Riemann-adelic.git
   cd Riemann-adelic
   ```

2. **Check system requirements**
   ```bash
   head -40 ENV.lock
   # Verify: Ubuntu 24.04, Python 3.12.3, x86_64
   ```

3. **Install dependencies**
   ```bash
   pip install -r requirements-lock.txt
   ```

4. **Verify dataset checksums**
   ```bash
   sha256sum Evac_Rpsi_data.csv
   # Expected: 412ab7ba54a5041ff12324650e8936995795c6abb7cfdb97d7a765a2c4ce7869
   ```

5. **Verify QCAL configuration**
   ```bash
   grep -A 4 "QCAL ∞³ CONFIGURATION" ENV.lock
   # Expected:
   # - Frequency: 141.7001 Hz
   # - Coherence C (from spectral moment): C = 244.36
   # - Universal C (eigenvalue-based): 629.83
   ```

6. **Run verification**
   ```bash
   python verify_environment_integrity.py
   # Must show: ✅ Verification PASSED
   ```

7. **Execute validations**
   ```bash
   # See results match published certificates in data/
   python validate_v5_coronacion.py
   ```

## Expected Results

After running validations, results should **exactly match**:

- **Numerical precision**: 30 decimal places for V5 Coronación
- **Spectral coherence**: 18.2σ detection significance
- **Critical line**: All zeros on Re(s) = 1/2
- **Lean 4 builds**: No `sorry` statements (complete proofs)

## Troubleshooting

### Python Version Mismatch

**Warning:** `Python version mismatch: expected 3.11, got 3.12`

**Action:** This is a warning, not an error. Results may still be reproducible, but for exact reproduction use Python 3.11.

### Dataset Checksum Mismatch

**Error:** `Dataset checksum mismatches detected`

**Action:** Dataset file has been modified. Re-download from repository or verify file integrity.

### Missing Packages

**Warning:** `Required packages not installed`

**Action:** Install missing packages:
```bash
pip install -r requirements-lock.txt
```

## Documentation

- **[ENV_LOCK_GUIDE.md](ENV_LOCK_GUIDE.md)**: Complete documentation
- **[REPRODUCIBILITY.md](REPRODUCIBILITY.md)**: Reproducibility guidelines
- **[README.md](README.md)**: Repository overview

## Contact

For audit support:
- **Email**: institutoconsciencia@proton.me
- **Issues**: https://github.com/motanova84/Riemann-adelic/issues
- **ORCID**: https://orcid.org/0009-0002-1923-0773

## License

ENV.lock and QCAL ∞³ framework:
- **License**: Creative Commons BY-NC-SA 4.0
- **Author**: José Manuel Mota Burruezo Ψ ✧ ∞³
- **Institution**: Instituto de Conciencia Cuántica (ICQ)

---

**Last Updated**: 2026-01-18  
**ENV.lock Version**: Comprehensive snapshot with dataset verification  
**QCAL Frequency**: 141.7001 Hz ∞³
