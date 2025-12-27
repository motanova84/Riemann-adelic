# Core Theorems towards a Complete Proof of the Riemann Hypothesis

This folder contains the **foundational theorems** that are missing pieces to 
transform the project from a *conditional + numerical framework* into a 
**full mathematical proof** of the Riemann Hypothesis (RH).

## Structure

- **rigidez_arquimediana.tex**  
  *Theorem of Archimedean Rigidity*:  
  Proves that the only admissible archimedean local factor compatible with 
  global reciprocity and functional symmetry is  
  \[
  \pi^{-s/2}\Gamma(s/2).
  \]

- **unicidad_paley_wiener.tex**  
  *Paley–Wiener Uniqueness with Multiplicities*:  
  Ensures that if a function shares order ≤1, symmetry, spectral measure of zeros 
  (with multiplicities), and normalization at \(s=1/2\), then it coincides identically with 
  \(\Xi(s)\).

- **de_branges.tex**  
  *de Branges Scheme for \(D(s)\)*:  
  Embeds \(D(s)\) into a de Branges space \(\mathcal{H}(E)\).  
  Positivity of the Hamiltonian ensures that the spectrum is real, forcing all zeros 
  of \(D(s)\) onto the critical line.

- **main.tex**  
  Collects all the theorems in a single PDF.

- **Makefile**  
  Simple build system to generate `main.pdf`.

## Compilation

```bash
cd docs/teoremas_basicos
make
```

This produces main.pdf with all core theorems.

## Purpose

These documents represent the mathematical backbone required to
elevate the framework from conditional validity to a Millennium Problem-level proof:

- Eliminate the dependency on ad hoc axioms (A1–A4).
- Derive the Archimedean factor rigorously.
- Ensure uniqueness of \(D(s) \equiv \Xi(s)\).
- Force analytically that all zeros lie on the critical line.

Together, they form the checklist of missing steps for a universally accepted resolution of RH.

**Author:** José Manuel Mota Burruezo  
**Affiliation:** Instituto Conciencia Cuántica – 2025

