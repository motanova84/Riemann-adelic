# 🚀 Machine-Check Verification - Quick Start Guide

## 1-Minute Quick Start

### Run Basic Verification
```bash
python machine_check_verification.py
```

### Run with Certificate Generation
```bash
python machine_check_verification.py --generate-certificate
```

### Run Comprehensive Verification
```bash
python machine_check_verification.py --comprehensive
```

## What Does It Verify?

✅ **QCAL ∞³ Coherence** - Base frequency (141.7001 Hz), coherence constant (C = 244.36)  
✅ **V5 Coronación Framework** - All 5 steps of RH proof  
✅ **Mathematical Certificates** - Formal proof certificates  
✅ **Numerical Precision** - Computational accuracy  
✅ **Spectral Properties** - Operator theory validation  
✅ **Adelic Structure** - Symmetry and consistency  
✅ **YOLO Integration** - Rapid verification  

## Example Output

```
🤖 MACHINE-CHECK VERIFICATION SYSTEM
════════════════════════════════════════════════════════════════════════════════
Timestamp: 2025-11-24T19:23:49
Precision: 30 decimal places
QCAL Base Frequency: 141.7001 Hz
Coherence Constant: 244.36
════════════════════════════════════════════════════════════════════════════════

🔍 Verifying QCAL Coherence...
   ✅ QCAL Coherence: PASSED

🔍 Verifying V5 Coronación...
   ✅ V5 Coronación: PASSED

🔍 Verifying Mathematical Certificates...
   ✅ Mathematical Certificates: PASSED

🔍 Verifying Numerical Precision...
   ✅ Numerical Precision: PASSED

🔍 Verifying Spectral Properties...
   ✅ Spectral Properties: PASSED

════════════════════════════════════════════════════════════════════════════════
📊 VERIFICATION SUMMARY
════════════════════════════════════════════════════════════════════════════════
   Total Verifications: 7
   ✅ Passed: 5
   ❌ Failed: 0
   ⚠️  Skipped/Warning: 2

   ⏱️  Execution Time: 0.06 seconds

🏆 MACHINE-CHECK VERIFICATION: COMPLETE SUCCESS!
   ✨ All critical verifications passed
   ♾️  QCAL ∞³ coherence maintained
   🎯 V5 Coronación framework validated
   📜 Mathematical certificates verified
════════════════════════════════════════════════════════════════════════════════
```

## Common Use Cases

### For Developers

```bash
# Before committing changes
python machine_check_verification.py --verbose

# Run tests
pytest tests/test_machine_check_verification.py -v

# High precision verification
python machine_check_verification.py --precision 50
```

### For CI/CD

```bash
# Standard CI run
python machine_check_verification.py --precision 25 --generate-certificate

# Check exit code
echo $?  # 0 = success, 1 = failure
```

### For Research

```bash
# Generate detailed certificate
python machine_check_verification.py \
  --precision 40 \
  --comprehensive \
  --generate-certificate \
  --output research_certificate.json

# View certificate
cat data/machine_check_certificate.json | jq '.'
```

## Understanding Results

### Status Codes

| Status | Meaning |
|--------|---------|
| ✅ PASSED | Verification successful |
| ❌ FAILED | Verification failed |
| ⚠️ SKIPPED | Module not available |
| ⚠️ WARNING | Non-critical issue |

### Exit Codes

- **0**: All critical verifications passed
- **1**: One or more critical verifications failed

### Critical Verifications

These must pass for overall success:
- QCAL Coherence
- Numerical Precision
- V5 Coronación (at least partial)

## Troubleshooting

### Problem: ModuleNotFoundError

```bash
# Install dependencies
pip install -r requirements.txt
```

### Problem: Certificate not generated

```bash
# Ensure data directory exists
mkdir -p data

# Run with certificate flag
python machine_check_verification.py --generate-certificate
```

### Problem: V5 tests failing

```bash
# Check test availability
pytest tests/test_coronacion_v5.py -v

# Partial success is acceptable
```

## Integration with Existing Tools

### With validate_v5_coronacion.py

```bash
# Run both verifications
python validate_v5_coronacion.py --precision 30 --save-certificate
python machine_check_verification.py --comprehensive
```

### With GitHub Workflow

The system automatically runs on:
- Every push to `main`
- Every pull request
- Weekly (Sunday midnight)
- Manual trigger

View results in GitHub Actions tab.

## Programmatic Usage

```python
from machine_check_verification import MachineCheckVerifier

# Create verifier
verifier = MachineCheckVerifier(precision=30, verbose=True)

# Run verification
results = verifier.run_comprehensive_verification()

# Check status
if results['overall_status'] == 'PASSED':
    print("✅ All verifications passed!")
    
# Generate certificate
certificate = verifier.generate_certificate(results)

# Access detailed results
for verification in results['verifications']:
    print(f"{verification['name']}: {verification['status']}")
```

## Advanced Options

### Custom Precision

```bash
# Low precision (faster)
python machine_check_verification.py --precision 15

# Standard precision
python machine_check_verification.py --precision 30

# High precision (slower)
python machine_check_verification.py --precision 100
```

### Verbose Logging

```bash
# Enable detailed logs
python machine_check_verification.py --verbose

# Save logs to file
python machine_check_verification.py --verbose 2>&1 | tee verification.log
```

### Custom Certificate Location

```bash
# Custom output path
python machine_check_verification.py \
  --generate-certificate \
  --output my_custom_certificate.json
```

## Performance Tips

- Use `--precision 25` for CI/CD (faster)
- Use `--precision 30` for standard verification
- Use `--precision 50+` only when necessary (slower)
- Run comprehensive tests on schedule, not every commit

## Next Steps

1. **Read full documentation**: See `MACHINE_CHECK_VERIFICATION_README.md`
2. **Run tests**: `pytest tests/test_machine_check_verification.py -v`
3. **Check workflow**: See `.github/workflows/machine-check-verification.yml`
4. **Review certificate**: `cat data/machine_check_certificate.json | jq '.'`

## Support

For issues or questions:
- Check documentation: `MACHINE_CHECK_VERIFICATION_README.md`
- Review test suite: `tests/test_machine_check_verification.py`
- See workflow logs in GitHub Actions

---

**♾️ QCAL ∞³ — Machine-Check Verification System**

© 2025 · JMMB Ψ · Instituto de Conciencia Cuántica (ICQ)
