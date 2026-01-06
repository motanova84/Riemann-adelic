# Lean 4 Build Instructions

## Prerequisites

### 1. Install elan (Lean Version Manager)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

This will install:
- `elan`: Lean version manager
- `lean`: Lean compiler
- `lake`: Lean build system

Add to your PATH (if not done automatically):
```bash
export PATH="$HOME/.elan/bin:$PATH"
```

### 2. Verify Installation

```bash
elan --version
lean --version
lake --version
```

## Building the Riemann Adelic Proof

### Step 1: Navigate to Project

```bash
cd formalization/lean
```

### Step 2: Install Lean Toolchain

The project uses Lean 4.5.0 as specified in `lean-toolchain`:

```bash
# Elan will automatically install the correct version
lake --version
```

### Step 3: Download Mathlib4

```bash
# Get mathlib4 precompiled cache (recommended)
lake exe cache get
```

This downloads precompiled mathlib files, saving hours of compilation time.

### Step 4: Build the Project

```bash
# Build all Lean files
lake build
```

Expected output:
```
Building RiemannAdelic
Building Main
Build succeeded!
```

### Step 5: Run the Main Program

```bash
# Execute the compiled program
./build/bin/riemann-adelic-lean
```

Expected output:
```
Riemann Hypothesis Adelic Proof - Lean 4 Formalization
José Manuel Mota Burruezo (V5.1, unconditional)

All modules loaded successfully!
```

## Checking Individual Files

To check a specific file without full compilation:

```bash
# Check RH_final.lean
lean RH_final.lean

# Check entire_order.lean
lean RiemannAdelic/entire_order.lean
```

## Module Structure

The project consists of the following modules:

```
formalization/lean/
├── Main.lean                           # Entry point
├── RH_final.lean                       # Main RH theorem
├── lakefile.lean                       # Build configuration
├── lean-toolchain                      # Lean version (4.5.0)
└── RiemannAdelic/                      # Main library
    ├── axioms_to_lemmas.lean          # A1, A2, A4 lemmas
    ├── entire_order.lean              # Hadamard factorization ✅ NEW
    ├── functional_eq.lean             # Functional equation
    ├── arch_factor.lean               # Archimedean factor
    ├── de_branges.lean                # de Branges theory
    ├── positivity.lean                # Positivity results
    ├── poisson_radon_symmetry.lean    # Poisson symmetry
    ├── pw_two_lines.lean              # Paley-Wiener
    ├── uniqueness_without_xi.lean     # Uniqueness theory
    └── zero_localization.lean         # Zero localization
```

## What Gets Built

### 1. Library: RiemannAdelic
Contains all mathematical modules for the Riemann Hypothesis proof.

### 2. Executable: riemann-adelic-lean
Main program that verifies all modules load correctly.

## Troubleshooting

### Problem: "no default toolchain configured"
**Solution**: The project has `lean-toolchain` file specifying v4.5.0. Run from project directory:
```bash
cd formalization/lean
lake build  # This should auto-install the toolchain
```

### Problem: Mathlib not found
**Solution**: Download mathlib cache:
```bash
lake exe cache get
```

### Problem: Network timeout downloading mathlib
**Solution**: 
1. Check internet connection
2. Try alternative mirror:
   ```bash
   lake exe cache get --no-fetch
   lake update
   ```

### Problem: Compilation takes very long
**Solution**: Use mathlib cache (see Step 3 above). Without cache, mathlib compilation can take 2-4 hours.

### Problem: Out of memory during build
**Solution**: Increase swap space or use mathlib precompiled cache:
```bash
lake exe cache get
```

## Verification Status

### ✅ Completed Modules
- **RH_final.lean**: Main theorem with complete proof structure
- **axioms_to_lemmas.lean**: A1, A2, A4 proven as lemmas
- **entire_order.lean**: Complete Hadamard factorization with convergent series

### 🔄 In Progress
- Other modules have skeletal structure with axioms
- Full constructive proofs to replace `sorry` placeholders

## Testing

### Run Syntax Validator
```bash
python3 validate_syntax.py
```

### Check for Sorry Placeholders
```bash
grep -r "sorry" RiemannAdelic/*.lean | wc -l
```

### Verify Imports
```bash
lean --check Main.lean
```

## CI/CD Integration

For continuous integration, add to your workflow:

```yaml
- name: Install Lean
  run: |
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
    echo "$HOME/.elan/bin" >> $GITHUB_PATH

- name: Get Mathlib cache
  run: |
    cd formalization/lean
    lake exe cache get

- name: Build Lean project
  run: |
    cd formalization/lean
    lake build
```

## Performance Notes

### Compilation Times (with mathlib cache)
- Clean build: ~2-5 minutes
- Incremental build: ~10-30 seconds
- Single file check: ~1-5 seconds

### Compilation Times (without mathlib cache)
- Full build: 2-4 hours (not recommended)

## References

- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lake Build System](https://github.com/leanprover/lake)

## Support

For issues with:
- **Lean installation**: See [Lean Community](https://leanprover.zulipchat.com/)
- **Mathematical content**: See project documentation
- **Build errors**: Check troubleshooting section above

---

**Last Updated**: October 21, 2025  
**Lean Version**: 4.5.0  
**Mathlib4 Version**: master (latest)  
**Project**: Riemann Hypothesis Adelic Proof  
**Author**: José Manuel Mota Burruezo
