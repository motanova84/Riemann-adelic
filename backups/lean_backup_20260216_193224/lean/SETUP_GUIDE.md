# Lean Formalization Setup and Activation Guide

## 🎯 Overview

This guide provides step-by-step instructions to **activate, validate, and work with** the Lean 4 formalization of the Riemann Hypothesis adelic proof.

**Current Status**: ✅ Structure validated, 🔄 In progress (87 sorries, 15.5% complete)

## 📋 Prerequisites

- **Operating System**: Linux, macOS, or Windows (WSL recommended)
- **Tools**: curl, git, python3
- **Disk Space**: ~2 GB for Lean toolchain and mathlib4

## 🚀 Installation Steps

### 1. Install elan (Lean Version Manager)

```bash
# Download and install elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Add elan to PATH (add to ~/.bashrc or ~/.zshrc for persistence)
export PATH="$HOME/.elan/bin:$PATH"

# Verify installation
elan --version
```

Expected output: `elan 4.x.x`

### 2. Navigate to the Lean Project

```bash
cd formalization/lean
```

### 3. Install Lean 4.5.0 Toolchain

The toolchain will be automatically installed based on `lean-toolchain` file:

```bash
# This will read lean-toolchain and install leanprover/lean4:v4.5.0
lake update
```

Alternatively, install manually:

```bash
elan toolchain install leanprover/lean4:v4.5.0
elan default leanprover/lean4:v4.5.0
```

### 4. Get mathlib4 Cache (Optional but Recommended)

This step downloads precompiled mathlib4 libraries to speed up compilation:

```bash
# Get cached mathlib binaries
lake exe cache get
```

**Note**: This requires ~1.5 GB download and may take 5-10 minutes.

### 5. Build the Project

```bash
# Build all Lean files
lake build
```

Expected behavior:
- First build may take 10-30 minutes (compiling mathlib4 dependencies)
- Subsequent builds are much faster (only recompile changed files)
- You'll see warnings about `sorry` placeholders - this is expected

### 6. Verify Installation

```bash
# Check that lean is available
lean --version

# Check that lake is available
lake --version
```

## 🔍 Validation

### Comprehensive Lean Environment Validation (Recommended)

Run the integrated shell validation script for complete environment verification:

```bash
# From formalization/lean directory
cd formalization/lean
./validate_lean_env.sh
```

This script performs:
- ✅ Lean 4 version verification
- ✅ Clean build environment (removes old artifacts)
- ✅ Dependency updates (mathlib4 cache)
- ✅ Full project compilation with timing
- ✅ Critical module verification (D_explicit, RH_final, de_branges, schwartz_adelic)
- ✅ Main theorem detection (riemann_hypothesis_adelic)
- ✅ Sorry marker detection (incomplete proofs)

### Python Validation Script (Alternative)

Run the Python validation script to check the formalization structure:

```bash
# From repository root
python3 validate_lean_formalization.py
```

This script checks:
- ✅ File structure integrity
- ✅ Import consistency
- ✅ Module completeness
- ✅ Proof status (theorems, axioms, sorries)
- ✅ Toolchain configuration

### Manual Validation

Check specific files:

```bash
cd formalization/lean

# Check Main.lean
lean Main.lean

# Check RH_final.lean (main theorem)
lean RH_final.lean

# Type check without building
lean --version RiemannAdelic/D_explicit.lean
```

## 📊 Current Formalization Status

Based on automated validation:

| Metric | Count | Status |
|--------|-------|--------|
| **Total Theorems/Lemmas** | 103 | ✅ |
| **Total Axioms** | 26 | ⚠️ Being reduced |
| **Sorry Placeholders** | 87 | 🔄 In progress |
| **Estimated Completeness** | 15.5% | 🔄 |

### Files with Most Work Remaining

1. `zero_localization.lean` - 13 sorries
2. `pw_two_lines.lean` - 11 sorries  
3. `D_explicit.lean` - 9 sorries
4. `positivity.lean` - 8 sorries
5. `de_branges.lean` - 7 sorries

### Fully Complete Modules

- ✅ `axioms_to_lemmas.lean` - 12 theorems, 0 sorries
- ✅ `arch_factor.lean` - 1 theorem, 0 sorries
- ✅ `axioms_to_lemmas_test.lean` - 1 theorem, 0 sorries

## 🛠️ Development Workflow

### Using VS Code with Lean Extension

1. **Install VS Code**: https://code.visualstudio.com/

2. **Install Lean 4 Extension**:
   - Open VS Code
   - Go to Extensions (Ctrl+Shift+X)
   - Search for "lean4"
   - Install the official Lean 4 extension

3. **Open the Project**:
   ```bash
   cd formalization/lean
   code .
   ```

4. **Features Available**:
   - Real-time type checking
   - Hover for documentation
   - Go to definition (F12)
   - Auto-completion
   - Error highlighting

### Working on Proofs

Example workflow for filling in `sorry` placeholders:

```lean
-- Before
theorem my_theorem : P → Q := by
  sorry

-- After
theorem my_theorem : P → Q := by
  intro h_P
  -- Use h_P to prove Q
  apply some_lemma
  exact h_P
```

### Building Incrementally

```bash
# Build only changed files
lake build

# Build specific module
lake build RiemannAdelic.D_explicit

# Clean and rebuild
lake clean
lake build
```

## 📚 Module Structure

The formalization is organized hierarchically:

```
Main.lean (entry point)
├── Core axioms
│   └── RiemannAdelic.axioms_to_lemmas
├── Constructive D(s)
│   ├── RiemannAdelic.schwartz_adelic
│   └── RiemannAdelic.D_explicit
├── Entire function theory
│   └── RiemannAdelic.entire_order
├── Functional equation
│   ├── RiemannAdelic.functional_eq
│   └── RiemannAdelic.poisson_radon_symmetry
├── de Branges spaces
│   └── RiemannAdelic.de_branges
├── Positivity theory
│   ├── RiemannAdelic.positivity
│   └── RiemannAdelic.doi_positivity
├── Zero localization
│   └── RiemannAdelic.zero_localization
├── Uniqueness
│   └── RiemannAdelic.uniqueness_without_xi
└── Paley-Wiener
    ├── RiemannAdelic.pw_two_lines
    └── RiemannAdelic.lengths_derived
```

## 🎯 Next Steps for Contributors

### Priority 1: Core Constructions (1-2 weeks)
- [ ] Complete `D_explicit.lean` - spectral trace computation
- [ ] Finish `schwartz_adelic.lean` - Fourier properties
- [ ] Prove membership: `D_explicit ∈ H_zeta.carrier`

### Priority 2: Supporting Theory (2-4 weeks)
- [ ] Complete `de_branges.lean` - Hilbert space structure
- [ ] Finish `positivity.lean` - trace class operators
- [ ] Complete `entire_order.lean` - Hadamard factorization

### Priority 3: Zero Localization (4-6 weeks)
- [ ] Complete `zero_localization.lean`
- [ ] Finish `pw_two_lines.lean` - Paley-Wiener theory
- [ ] Complete `uniqueness_without_xi.lean`

### Priority 4: Final Integration (6-8 weeks)
- [ ] Reduce remaining axioms to theorems
- [ ] Replace all `sorry` with complete proofs
- [ ] Full compilation and testing
- [ ] Documentation and examples

## 🐛 Troubleshooting

### Issue: "elan not found"

**Solution**: Add elan to PATH:
```bash
export PATH="$HOME/.elan/bin:$PATH"
```

### Issue: "lake: command not found"

**Solution**: Ensure Lean toolchain is installed:
```bash
elan toolchain install leanprover/lean4:v4.5.0
```

### Issue: "mathlib not found"

**Solution**: Update dependencies:
```bash
lake update
lake exe cache get
```

### Issue: Build takes too long

**Solution**: Use mathlib cache:
```bash
lake exe cache get
```

### Issue: Out of memory during build

**Solution**: Limit parallel jobs:
```bash
LEAN_JOBS=1 lake build
```

## 📖 Resources

### Official Lean 4 Documentation
- **Lean 4 Manual**: https://leanprover.github.io/lean4/doc/
- **Theorem Proving in Lean 4**: https://leanprover.github.io/theorem_proving_in_lean4/
- **Mathlib4 Documentation**: https://leanprover-community.github.io/mathlib4_docs/

### Lean Community
- **Zulip Chat**: https://leanprover.zulipchat.com/
- **Lean Community**: https://leanprover-community.github.io/

### This Project
- **Paper**: DOI 10.5281/zenodo.17116291
- **Repository**: https://github.com/motanova84/-jmmotaburr-riemann-adelic
- **Formalization Status**: See `FORMALIZATION_STATUS.md`

## ✅ Verification Checklist

Use this checklist to verify your setup:

- [ ] elan installed and in PATH
- [ ] Lean 4.5.0 toolchain installed
- [ ] lake command available
- [ ] Project builds without errors (warnings OK)
- [ ] VS Code + Lean 4 extension installed (optional)
- [ ] `validate_lean_formalization.py` runs successfully
- [ ] Can open and edit `.lean` files
- [ ] Type checking works in real-time (if using VS Code)

## 🎓 Learning Path

If you're new to Lean:

1. **Start with**: "Theorem Proving in Lean 4" (online book)
2. **Practice**: Natural number game (https://adam.math.hhu.de/#/g/leanprover-community/NNG4)
3. **Study**: Simple modules like `arch_factor.lean`
4. **Contribute**: Pick a `sorry` in a completed module and try to fill it in
5. **Ask**: Use Lean Zulip chat for questions

## 📞 Support

For questions or issues:
- **GitHub Issues**: Open an issue in the repository
- **Email**: motanova84@github.com
- **Lean Zulip**: Ask in #new members or #mathlib4

---

**Last Updated**: October 2025  
**Version**: 1.0  
**Maintainer**: José Manuel Mota Burruezo
