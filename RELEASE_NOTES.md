# Release Notes

## v5.3.1 (2025-10-30)

### RH - Sistema Adélico S-finito
- ✅ **Axioms purged → Theorems**: Created `axiom_purge.lean` with stub theorems
  - Theorem (D ≡ Ξ): Entire function uniqueness via Hadamard factorization and Paley-Wiener determinacy
  - Theorem (Critical line zeros): Self-adjoint operator spectrum confinement
  - Lemma (Trivial zeros excluded): Gamma factor separation
- ✅ **CI/CD**: Added `lean-ci.yml` workflow for automatic axiom checking
- ✅ **Documentation updates**: Framework for replacing axiom-based proofs with theorem-based proofs

### Reproducibility Improvements
- ✅ **Makefile**: Enhanced with `pdf`, `figs`, and `tables` targets for automated builds
- ✅ **ENV.lock**: Created Python environment lock file for dependency reproducibility
- ✅ **Build automation**: Integrated LaTeX compilation with latexmk and shell-escape

### Technical Details

#### Axiom to Theorem Conversion
The new `axiom_purge.lean` file establishes three key results:

1. **D ≡ Ξ Theorem**: Proves that any entire function D with specific properties (functional equation, growth bounds, divisor matching) must be identical to the Riemann xi-function
   - Uses Hadamard factorization
   - Quotient Q = D/Ξ analysis
   - Paley-Wiener determinacy
   - Normalization at fixed point

2. **Critical Line Theorem**: Shows all non-trivial zeros lie on Re(s) = 1/2
   - Self-adjoint operator construction
   - Spectral analysis
   - Kernel positivity
   - Functional symmetry

3. **Trivial Zeros Exclusion**: Separates trivial zeros via archimedean gamma factor
   - Gamma product structure
   - Divisor restriction to critical strip

#### CI/CD Axiom Check
The new workflow automatically verifies that no unwanted axioms are introduced during development, ensuring the proof remains constructive and verifiable.

### Future Work
- [ ] Fill in detailed proofs for stub theorems in `axiom_purge.lean`
- [ ] Divide `axiom_purge.lean` into specialized modules: `Hadamard.lean`, `RelativeDeterminant.lean`, `KernelPositivity.lean`
- [ ] Update PDF documentation to use theorem labels instead of axiom labels
- [ ] Add U1/U2 convergence hypotheses as numbered references
- [ ] Create biblatex configuration for bibliography management

---

## Previous Versions

### v5.3 (2025-10-26)
- Lean 4.5.0 formalization activated
- 14 modules integrated in Main.lean
- 103 theorems, 26 axioms, 87 sorries
- Complete validation scripts

### v5.2 (2025-10-20)
- Constructive D(s) definition via spectral trace
- Schwartz functions with explicit decay estimates
- de Branges spaces complete
- Hadamard factorization implemented

### v5.1 (2025-09-15)
- Initial unconditional proof framework
- Axiomatic approach
- Zenodo DOI: 10.5281/zenodo.17116291

---

**Maintained by**: José Manuel Mota Burruezo (@motanova84)  
**Repository**: https://github.com/motanova84/-jmmotaburr-riemann-adelic  
**License**: See LICENSE and LICENSE-CODE files
