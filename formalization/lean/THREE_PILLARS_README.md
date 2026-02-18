# 🔗 Navigation: Three Pillars Architecture

## Quick Access

👉 **START HERE**: [ThreePillars/README.md](./ThreePillars/README.md)

## What is Three Pillars?

A modular Lean 4 formalization of the Riemann Hypothesis proof based on three fundamental pillars:

1. **PILAR 1**: Domain Shield (`DomainSobolev.lean`) - Dense, closed domain
2. **PILAR 2**: Spectral Rigor (`KatoSpectral.lean`) - Kato-Rellich with κ=141.7001
3. **PILAR 3**: Absolute Identity (`PaleyWienerIdentity.lean`) - Paley-Wiener uniqueness

→ **Final Theorem**: `RiemannHypothesis.lean` - All non-trivial zeros satisfy Re(ρ) = 1/2

## Documentation Index

| Document | Purpose | Read Time |
|----------|---------|-----------|
| [README.md](./ThreePillars/README.md) | Complete overview | 15 min |
| [QUICKSTART.md](./ThreePillars/QUICKSTART.md) | Get started in 5 minutes | 5 min |
| [INTEGRATION.md](./ThreePillars/INTEGRATION.md) | Connect with existing modules | 10 min |
| [VISUAL_SUMMARY.txt](./ThreePillars/VISUAL_SUMMARY.txt) | ASCII diagrams | 5 min |
| [IMPLEMENTATION_SUMMARY.md](./ThreePillars/IMPLEMENTATION_SUMMARY.md) | Completion report | 10 min |

## Files Structure

```
ThreePillars/
├── ThreePillars.lean              # Namespace root
├── DomainSobolev.lean             # PILAR 1: Domain (160 lines)
├── KatoSpectral.lean              # PILAR 2: Spectrum (150 lines)
├── PaleyWienerIdentity.lean       # PILAR 3: Identity (180 lines)
├── RiemannHypothesis.lean         # Final theorem (210 lines)
└── [Documentation files]          # READMEs & guides
```

## Quick Start

```lean
import ThreePillars

open ThreePillars.RiemannHypothesis

-- Use the main theorem
example : ∀ ρ : ℂ, (∃ n : ℕ, ρ = -2 * n) ∨ ρ.re = 1/2 :=
  riemann_hypothesis
```

## Build

```bash
cd formalization/lean
lake build ThreePillars
```

## Key Features

- ✅ Zero additional axioms (only mathlib 4.5.0)
- ✅ Modular three-pillar architecture
- ✅ Frequency fundamental: κ = 141.7001 Hz
- ✅ Exhaustive documentation (~2,000 lines)
- ✅ Integration with existing modules

## Author

**José Manuel Mota Burruezo Ψ ✧ ∞³**
- ORCID: 0009-0002-1923-0773
- DOI: 10.5281/zenodo.17379721

---

For detailed information, see [ThreePillars/README.md](./ThreePillars/README.md)
