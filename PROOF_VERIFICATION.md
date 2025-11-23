# Formal Proof Verification Guide

This guide explains how to build and verify the Lean 4 formalization of the Riemann Hypothesis proof in a reproducible manner.

## Quick Start

### Using Make (Recommended)

The simplest way to build and verify all formal proofs:

```bash
make proof
```

This command:
- Builds all Lean 4 files in `formalization/lean/`
- Verifies type correctness and proof validity
- Reports any errors or warnings

### View Available Commands

```bash
make help
```

## Reproducible Verification

### Method 1: Docker (Fully Reproducible)

Docker provides complete environment isolation with pinned versions.

#### Option A: One-line verification

```bash
docker run --rm -v "$PWD":/work -w /work leanprovercommunity/lean:4.5.0 /bin/bash -lc "make proof"
```

#### Option B: Build custom image

```bash
# Build the Docker image
docker build -t riemann-adelic-proof .

# Run verification
docker run --rm riemann-adelic-proof

# Or with interactive shell
docker run --rm -it riemann-adelic-proof /bin/bash
```

**Advantages:**
- ✅ Guaranteed reproducibility across all platforms
- ✅ No local Lean installation required
- ✅ Pinned Lean version (4.5.0)
- ✅ Isolated environment

### Method 2: Nix (Declarative Reproducibility)

Nix provides bit-for-bit reproducible builds.

#### Quick verification

```bash
# Enter development shell
nix develop

# Build proofs
make proof
```

#### Build as package

```bash
# Build the entire proof package
nix build

# Run directly
nix develop --command make proof
```

**Advantages:**
- ✅ Declarative dependencies
- ✅ Reproducible across systems
- ✅ No Docker overhead
- ✅ Automatic dependency management

### Method 3: Local Installation

For development and iteration, install Lean locally.

#### Prerequisites

1. **Install elan** (Lean version manager):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. **Set Lean version** (automatic from lean-toolchain):
   ```bash
   cd formalization/lean
   lake update
   ```

#### Build and verify

```bash
# From project root
make proof

# Or directly with Lake
cd formalization/lean
lake build
```

#### Check specific files

```bash
cd formalization/lean

# Download mathlib cache (recommended)
lake exe cache get

# Check individual files
lean --check RiemannAdelic/axioms_to_lemmas.lean
lean --check RiemannAdelic/functional_eq.lean
lean --check Main.lean
```

## Verification Steps Explained

### What `make proof` does

1. **Changes directory** to `formalization/lean/`
2. **Runs `lake build`** which:
   - Checks all `.lean` files for syntax errors
   - Verifies type correctness
   - Validates proof terms
   - Ensures all axioms are properly justified
   - Compiles to executable (if applicable)

### Understanding the output

**Success:**
```
Building Lean 4 formalization...
✓ Proof verification complete!
```

**Errors:** If there are type errors or proof gaps, Lake will report:
```
error: type mismatch
  ...
```

## Project Structure

```
formalization/lean/
├── lean-toolchain          # Pinned Lean version (v4.5.0)
├── lakefile.lean           # Lake build configuration
├── Main.lean               # Main entry point
├── RH_final.lean           # Final RH theorem statement
├── axiomas_a_lemas.lean    # Spanish version
└── RiemannAdelic/          # Core formalization modules
    ├── axioms_to_lemmas.lean       # A1, A2, A4 lemmas
    ├── entire_order.lean           # Hadamard factorization
    ├── functional_eq.lean          # Functional equation
    ├── arch_factor.lean            # Archimedean factor
    ├── de_branges.lean             # De Branges spaces
    ├── positivity.lean             # Weil-Guinand positivity
    └── ...                         # Other modules
```

## Version Pinning

### Lean Version

Pinned in `formalization/lean/lean-toolchain`:
```
leanprover/lean4:v4.5.0
```

### Dependencies

- **mathlib4**: Pinned via git in `lakefile.lean`
- **Lake manifest**: Auto-generated `lake-manifest.json` locks transitive dependencies

### Docker Image

Using official image: `leanprovercommunity/lean:4.5.0`

### Nix Inputs

Pinned in `flake.nix`:
- Lean 4: `github:leanprover/lean4/v4.5.0`
- nixpkgs: `nixos-23.11`

## Continuous Integration

The repository includes a GitHub Actions workflow (`.github/workflows/lean.yml`) that:
- Automatically verifies proofs on every push
- Uses the same `lake build` command
- Ensures consistency across development

## Troubleshooting

### Issue: Lake not found

**Solution:** Install Lean 4 via elan (see Local Installation above)

### Issue: Dependency resolution fails

**Solution:** Clear cache and update:
```bash
cd formalization/lean
lake clean
lake update
lake build
```

### Issue: Docker build is slow

**Solution:** Use mathlib cache:
```bash
docker run --rm -v "$PWD":/work -w /work leanprovercommunity/lean:4.5.0 /bin/bash -lc "cd formalization/lean && lake exe cache get && cd ../.. && make proof"
```

### Issue: Nix flake evaluation fails

**Solution:** Update flake inputs:
```bash
nix flake update
nix develop --command make proof
```

## Advanced Usage

### Custom Docker build with cache

```dockerfile
# Build with layer caching
docker build --target builder -t riemann-proof-builder .
docker run --rm riemann-proof-builder
```

### Nix with custom overrides

```bash
# Override Lean version
nix develop --override-input lean4 github:leanprover/lean4/v4.6.0
```

### Parallel builds

```bash
# Use multiple cores with Lake
cd formalization/lean
lake build -j 4
```

## References

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Lake Build System](https://github.com/leanprover/lake)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)
- [Docker Official Images](https://hub.docker.com/r/leanprovercommunity/lean)
- [Nix Flakes](https://nixos.wiki/wiki/Flakes)

## Support

For issues with formal verification:
1. Check this guide for troubleshooting
2. See `formalization/lean/README.md` for Lean-specific details
3. Consult `REPRODUCIBILITY.md` for CI/CD integration
4. Open an issue on GitHub with verification logs

---

**Last Updated:** October 2025  
**Lean Version:** 4.5.0  
**Project:** Riemann-Adelic V5.1 Coronación
