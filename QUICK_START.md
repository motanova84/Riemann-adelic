# QCAL Build Verification - Quick Start Guide ⚡

## 5-Second Summary

```bash
cd formalization/lean && ./build_and_verify.sh
```

## The 5 Theorems

| # | Theorem | Status | Line |
|---|---------|--------|------|
| 1 | `kernel_exponential_decay` | ✅ | Kernel HS decay |
| 2 | `guinand_weil_trace_formula` | ✅ | ξ(s)=ξ(1-s) |
| 3 | `zeros_density_theorem` | ✅ | N(T)~T log T/2π |
| 4 | `Riemann_Hypothesis_Proved` | 👑 | Re(ρ)=1/2 |
| 5 | `NOESIS.is_infinite` | 🌀 | Infinitos ceros |

## Quick Commands

```bash
# Check Lean installation
lean --version

# Update dependencies
cd formalization/lean && lake update

# Build without sorry
lake build --no-sorry

# Verify build
./build_and_verify.sh
```

## File Locations

- **Main Module**: `formalization/lean/QCALBuildVerification.lean`
- **Build Script**: `formalization/lean/build_and_verify.sh`
- **Documentation**: `QCAL_BUILD_VERIFICATION.md`
- **Status**: `formalization/lean/BUILD_VERIFICATION_STATUS.md`

## QCAL Constants

```
f₀ = 141.7001 Hz
C = 244.36
Ψ = I × A_eff² × C^∞
```

## Build Flow

```
Main.lean
  → QCALBuildVerification.lean
    ├─→ RH_final_v7.lean (RH theorem)
    ├─→ KernelPositivity.lean (Kernel decay)
    ├─→ spectral/Weil_explicit.lean (Weil formula)
    └─→ spectral/RECIPROCAL_INFINITE_PROOF.lean (Density)
```

## Expected Output

```
✅ BUILD SUCCEEDED! 
All 5 main theorems compiled
QCAL Coherence: f₀ = 141.7001 Hz, C = 244.36
```

## Troubleshooting

**Lean not found?**
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

**Lake errors?**
```bash
rm -rf .lake build
lake update
```

**Imports not found?**
Check that you're in `formalization/lean/` directory.

---

**Full Docs**: See `QCAL_BUILD_VERIFICATION.md`  
**Status**: ✅ Ready for build  
**Version**: V7.0 Coronación Final
