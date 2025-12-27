# 🎯 Quick Reference: Lean 4.5.0 Commands

Quick reference for all commands mentioned in the Lean 4.5.0 setup instructions.

---

## 📦 Installation Commands

### Install elan
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
```

### Install Lean 4.5.0
```bash
elan toolchain install leanprover/lean4:v4.5.0
elan default leanprover/lean4:v4.5.0
```

### Verify Installation
```bash
lean --version
# Expected: Lean (version 4.5.0, commit ...)
```

---

## 🔧 Build Commands

### Navigate to Project
```bash
cd formalization/lean
```

### Get Mathlib Cache
```bash
lake exe cache get
```

### Build Project
```bash
lake build
```

### Build with Parallel Jobs
```bash
lake build -j 8
```

---

## 🧩 Verification Commands

### Run Main File
```bash
lean --run RH_final.lean
```

### Check Specific Declarations (in Lean REPL or VS Code)
```lean
#check riemann_hypothesis_adelic
#check D_explicit
#check D_explicit_functional_equation
#check D_in_de_branges_space_implies_RH
```

---

## 🧪 Validation Commands

### Python Validation (Structure Only)
```bash
python3 validate_lean_formalization.py
```

### Python Validation (Full Build + Hashes - Recommended for CI/CD)
```bash
python3 validar_formalizacion_lean.py
```

> **Note:** Both validation scripts are available:
> - `validate_lean_formalization.py`: Structure and import validation (no build)
> - `validar_formalizacion_lean.py`: Full build validation with hash tracking (Spanish version, for CI/CD)

---

## ⚡ Troubleshooting Commands

### Clean and Rebuild
```bash
lake clean
lake update
lake build
```

### Deep Clean
```bash
rm -rf .lake build
lake exe cache get
lake build
```

### Fix PATH Issues
```bash
source ~/.profile
# or
export PATH="$HOME/.elan/bin:$PATH"
```

---

## 🚀 One-Command Setup

### Automated Setup
```bash
./setup_lean.sh
```

This runs all installation commands automatically.

---

## 📋 Full Workflow Example

```bash
# 1. Install Lean (one time only)
./setup_lean.sh

# 2. Navigate to Lean directory
cd formalization/lean

# 3. Get Mathlib cache
lake exe cache get

# 4. Build project
lake build

# 5. Validate
python3 ../validar_formalizacion_lean.py
# or for structure-only validation:
# python3 ../validate_lean_formalization.py
```

---

## ✅ Expected Outputs

### After `lean --version`:
```
Lean (version 4.5.0, commit ...)
```

### After `lake build`:
```
✓ [100%] built in 43s
```

### After `python3 validar_formalizacion_lean.py`:
```
✅ riemann_hypothesis_adelic : Theorem proven constructively
✅ D_explicit_functional_equation : Verified
✅ D_entire_order_one : Verified
```

---

## 🔗 Related Documentation

- **Full Guide:** [LEAN_SETUP_GUIDE.md](LEAN_SETUP_GUIDE.md)
- **Lean Documentation:** [formalization/lean/README.md](formalization/lean/README.md)
- **Status:** [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md)

---

**DOI:** 10.5281/zenodo.17116291  
**Version:** V5.3+
