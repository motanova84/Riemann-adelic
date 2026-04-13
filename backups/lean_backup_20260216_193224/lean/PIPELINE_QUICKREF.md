# 📋 Pipeline Quick Reference

**RH Proof Build & Verification - Command Reference**

---

## 🚀 One-Line Execution

```bash
cd formalization/lean && ./scripts/complete_pipeline.sh
```

---

## 📝 Step-by-Step Commands

### 1️⃣ Clean Build
```bash
lake clean
```

### 2️⃣ Compile
```bash
lake build
```

### 3️⃣ Verify No Sorries
```bash
# Lean script (requires build):
lake env lean --run scripts/verify_no_sorrys.lean

# Python script (faster):
python3 scripts/verify_no_sorrys.py
```

### 4️⃣ Generate Hash
```bash
./scripts/generate_hash.sh
```

---

## 🔧 Common Operations

### Install Lean 4.5.0
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
elan toolchain install leanprover/lean4:v4.5.0
elan default leanprover/lean4:v4.5.0
```

### Get Mathlib Cache (faster builds)
```bash
lake exe cache get
```

### Update Dependencies
```bash
lake update
```

### Build with Limited Parallelism
```bash
lake build -j 2
```

### Verify Hash
```bash
sha256sum -c build/rh_proof.sha256
```

---

## 📊 Status Checks

### Check Lean Version
```bash
lean --version  # Should be: Lean (version 4.5.0, ...)
```

### Check Build Status
```bash
lake build 2>&1 | tail -n 20
```

### Count Sorries
```bash
python3 scripts/verify_no_sorrys.py | grep "Total sorries"
```

### View Generated Hash
```bash
cat build/rh_proof.hash
cat build/rh_proof.sha256
cat build/rh_proof.metadata
```

---

## ✅ Success Indicators

| Check | Command | Expected |
|-------|---------|----------|
| Build | `lake build` | `Build completed successfully.` |
| Sorries | `python3 scripts/verify_no_sorrys.py` | `0 sorries found` |
| Hash | `sha256sum -c build/rh_proof.sha256` | `OK` |

---

## 🔥 Emergency Quick Fixes

### Build Stuck?
```bash
pkill lake  # Kill stuck processes
lake clean
lake build
```

### Network Issues?
```bash
lake exe cache get  # Download pre-built cache
lake build
```

### Out of Memory?
```bash
lake build -j 1  # Single-threaded build
```

### Type Errors?
```bash
lake update      # Update dependencies
lake clean       # Clean everything
lake build       # Fresh build
```

---

## 🎯 QCAL Parameters

- **Frequency**: 141.7001 Hz
- **Coherence**: C = 244.36
- **DOI**: 10.5281/zenodo.17379721

---

## 📚 More Info

- Full guide: `PIPELINE_EXECUTION_GUIDE.md`
- Scripts: `scripts/README.md`
- Setup: `SETUP_GUIDE.md`
- Main: `README.md`
