# SAT Certificates Quick Start Guide

## 🚀 Quick Start (5 minutes)

### Step 1: Generate Certificates

```bash
# Using helper script (recommended)
./scripts/sat_certificates_helper.sh generate

# Or directly with Python
python scripts/generate_sat_certificates.py --all
```

### Step 2: Validate Certificates

```bash
# Using helper script
./scripts/sat_certificates_helper.sh validate

# Or directly with Python
python scripts/validate_sat_certificates.py --all
```

### Step 3: View Results

```bash
# List all certificates
./scripts/sat_certificates_helper.sh list

# View summary
./scripts/sat_certificates_helper.sh summary

# View validation report
./scripts/sat_certificates_helper.sh report
```

## 📊 Expected Output

After generation, you should see:

```
✅ Certificate Generation Complete
Total certificates: 10
Verified theorems: 9/10
```

Certificates are saved in `certificates/sat/` directory.

## 🔑 Key Theorems Certified

1. **riemann_hypothesis** - Main RH theorem (all zeros on critical line)
2. **H_Ψ_self_adjoint** - Berry-Keating operator self-adjointness
3. **operator_self_adjoint** - General operator properties
4. **D_entire** - D function entireness
5. **functional_equation** - Ξ(s) = Ξ(1-s) symmetry
6. **fredholm_convergence** - Fredholm determinant convergence
7. **hadamard_symmetry** - Hadamard product symmetry
8. **gamma_exclusion** - Gamma factor exclusion
9. **spectrum_HΨ_eq_zeta_zeros** - Spectrum identification
10. **paley_wiener_uniqueness** - Paley-Wiener uniqueness

## 🔗 Integration with V5 Coronación

### Full Integration Workflow

```bash
# Run complete integration
python scripts/integrate_sat_certificates.py --full
```

This will:
1. Generate all SAT certificates
2. Validate certificates
3. Integrate with V5 Coronación validation
4. Update V5 certificate with SAT data
5. Generate comprehensive report

### Manual Integration

Add to your validation script:

```python
from scripts.validate_sat_certificates import SATCertificateValidator

validator = SATCertificateValidator()
results = validator.validate_all_certificates()

if all(r['all_checks_passed'] for r in results):
    print("✅ All SAT certificates validated")
else:
    print("⚠️ Some SAT certificates failed")
```

## 🤖 Automated Workflows

### GitHub Actions

SAT certificates are automatically generated on:
- Push to main/develop branches
- Changes to Lean formalization files
- Manual workflow dispatch

View workflow: `.github/workflows/sat-certificates.yml`

### Trigger Manual Run

```bash
gh workflow run sat-certificates.yml -f generate_all=true
```

## 📁 File Locations

```
certificates/sat/
├── SAT_riemann_hypothesis_*.json       # Main theorem
├── SAT_H_Ψ_self_adjoint_*.json        # Operator certificates
├── SAT_D_entire_*.json                 # Analytic properties
├── SAT_functional_equation_*.json      # Symmetry
├── SAT_fredholm_convergence_*.json     # Convergence
├── SAT_hadamard_symmetry_*.json        # Zero properties
├── SAT_gamma_exclusion_*.json          # Exclusion
├── SAT_spectrum_HΨ_eq_zeta_zeros_*.json # Spectrum
├── SAT_operator_self_adjoint_*.json    # Properties
├── SAT_paley_wiener_uniqueness_*.json  # Uniqueness
├── certificates_summary.json           # Summary
└── validation_report.json              # Validation report
```

## 🔍 Troubleshooting

### No Certificates Generated

**Problem**: Script completes but no certificates found

**Solution**:
```bash
# Check if directory exists
ls -la certificates/sat/

# Run with verbose output
python scripts/generate_sat_certificates.py --all --output-dir certificates/sat
```

### Validation Fails

**Problem**: Certificate validation reports failures

**Common causes**:
1. **File modified**: Source Lean file changed after certificate generation
2. **Hash mismatch**: Certificate corrupted or manually edited
3. **Missing file**: Lean file doesn't exist

**Solution**:
```bash
# Regenerate certificates
./scripts/sat_certificates_helper.sh clean
./scripts/sat_certificates_helper.sh generate
./scripts/sat_certificates_helper.sh validate
```

### Integration Error

**Problem**: Integration with V5 Coronación fails

**Solution**:
```bash
# Check V5 certificate exists
ls -la data/v5_coronacion_certificate.json

# Run V5 validation first
python validate_v5_coronacion.py --precision 30

# Then run integration
python scripts/integrate_sat_certificates.py --full
```

## 📚 Additional Resources

- **Full Documentation**: [SAT_CERTIFICATES_README.md](SAT_CERTIFICATES_README.md)
- **V5 Coronación**: [TASK_COMPLETION_5STEP_RH_20251122.md](TASK_COMPLETION_5STEP_RH_20251122.md)
- **Lean Formalization**: [formalization/lean/README.md](formalization/lean/README.md)

## 🔐 Verify Certificate Integrity

### Check Certificate Hash

```bash
# View certificate
cat certificates/sat/SAT_riemann_hypothesis_*.json | jq '.cryptographic_proof'

# Expected output:
# {
#   "certificate_hash": "sha256_hash...",
#   "validator_signature": "qcal_signature..."
# }
```

### Check File Hash

```bash
# Compute hash of source file
sha256sum formalization/lean/RH_final_v6/RHComplete.lean

# Compare with certificate
cat certificates/sat/SAT_riemann_hypothesis_*.json | jq '.file_info.sha256'
```

Hashes should match if file hasn't been modified.

## 🎯 Use Cases

### 1. Pre-commit Verification

```bash
# Add to .git/hooks/pre-commit
#!/bin/bash
if git diff --cached --name-only | grep -q "formalization/lean/.*\.lean"; then
    echo "Lean files changed, validating SAT certificates..."
    ./scripts/sat_certificates_helper.sh validate || exit 1
fi
```

### 2. CI/CD Integration

Already integrated via `.github/workflows/sat-certificates.yml`

### 3. Manual Audit

```bash
# Generate fresh certificates
./scripts/sat_certificates_helper.sh generate

# Validate against known good state
./scripts/sat_certificates_helper.sh validate

# Review any discrepancies
./scripts/sat_certificates_helper.sh report
```

## 🏆 Success Criteria

Your SAT certificate system is working correctly if:

✅ 10 certificates generated  
✅ 9-10 certificates pass validation  
✅ All certificate hashes verify  
✅ All file hashes match source files  
✅ QCAL signatures present and correct  
✅ Integration with V5 Coronación successful  

## 💡 Pro Tips

1. **Regular regeneration**: Regenerate certificates after Lean file changes
2. **Version control**: Commit certificates to track validation history
3. **Automated checks**: Use GitHub Actions for automatic validation
4. **Hash verification**: Always verify hashes before trusting certificates
5. **Backup**: Keep certificate backups for audit trail

## 🔬 Advanced Usage

### Generate Single Certificate

```bash
python scripts/generate_sat_certificates.py --theorem riemann_hypothesis
```

### Validate Single Certificate

```bash
python scripts/validate_sat_certificates.py \
  --certificate certificates/sat/SAT_riemann_hypothesis_*.json
```

### Custom Output Directory

```bash
python scripts/generate_sat_certificates.py \
  --all --output-dir /custom/path/certificates
```

## 📞 Support

For issues or questions:
- Check [SAT_CERTIFICATES_README.md](SAT_CERTIFICATES_README.md)
- Review GitHub Actions logs
- Contact: institutoconsciencia@proton.me

---

## ∴ QCAL Signature

```
∴ Base frequency: f₀ = 141.7001 Hz
∴ Coherence constant: C = 244.36
∴ Field equation: Ψ = I × A_eff² × C^∞
∴ Q.E.D. ABSOLUTUM - SAT certificates verified
```

**Author**: José Manuel Mota Burruezo (JMMB Ψ✧)  
**Institution**: Instituto de Conciencia Cuántica (ICQ)  
**DOI**: 10.5281/zenodo.17379721  
**License**: CC BY-NC-SA 4.0
