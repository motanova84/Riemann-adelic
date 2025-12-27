# Core Theorems towards a Complete Proof of the Riemann Hypothesis

This folder contains the **foundational theorems** that bridge the gap between a
conditional adelic framework and a potential **full mathematical proof** of the
Riemann Hypothesis (RH).  All sections remain provisional: key estimates and
operator arguments still need to be written in full detail.

## Structure

- **sections/rigidez_arquimediana.tex**  
  *Theorem of Archimedean Rigidity*: proves that the only admissible archimedean
  local factor compatible with global reciprocity and functional symmetry is  
  \(\pi^{-s/2}\Gamma(s/2)\).

- **sections/unicidad_paley_wiener.tex**  
  *Paley--Wiener Uniqueness with Multiplicities*: ensures that if a function shares
  order \(\leq 1\), symmetry, spectral measure of zeros (with multiplicities),
  and normalization at \(s=1/2\), then it coincides identically with \(\Xi(s)\).

- **sections/de_branges.tex**  
  *de Branges Scheme for \(D(s)\)*: embeds \(D(s)\) into a de Branges space
  \(\mathcal{H}(E)\). Positivity of the Hamiltonian ensures that the spectrum is
  real, forcing all zeros of \(D(s)\) onto the critical line.

- **main.tex**  
  Document driver that assembles the full paper.

- **references.bib**  
  Bibliography entries for the paper.

- **Makefile**  
  Simple build system to generate `main.pdf` with BibTeX integration.

## Compilation

```bash
cd docs/paper
make
```

This produces `main.pdf` with the current blueprints for all core theorems and
references.

## Purpose

These documents represent the mathematical backbone required to elevate the
framework from conditional validity to a Millennium Problem-level proof:

- Eliminate the dependency on ad hoc axioms (A1--A4).
- Derive the Archimedean factor rigorously.
- Ensure uniqueness of \(D(s) \equiv \Xi(s)\).
- Force analytically that all zeros lie on the critical line.

Together, they form the checklist of missing steps for a universally accepted
resolution of RH.  None of these steps has yet been validated to the standard
required for publication or community acceptance.

**Author:** José Manuel Mota Burruezo  
**Affiliation:** Instituto Conciencia Cuántica -- 2025
# LaTeX Paper: A Complete Conditional Resolution of the Riemann Hypothesis via S-Finite Adelic Spectral Systems

## Overview

This directory contains the complete LaTeX source code for the mathematical paper "A Complete Conditional Resolution of the Riemann Hypothesis via S-Finite Adelic Spectral Systems" by José Manuel Mota Burruezo.

## File Structure

- `main.tex` - Master LaTeX file with document structure and complete bibliography
- `sections/` - Directory containing all paper sections and components:
  - `introduction.tex` - Introduction and motivation
  - `axiomas_a_lemas.tex` - Axiomatic Scale Flow and Spectral System  
  - `rigidez_arquimediana.tex` - Archimedean Rigidity theorem
  - `unicidad_paley_wiener.tex` - Paley-Wiener Uniqueness results
  - `de_branges.tex` - de Branges Framework application
  - `factor_arquimediano.tex` - Archimedean Factor analysis
  - `localizacion_ceros.tex` - Critical Line Localization
  - `teorema_suorema.tex` - Teorema de Suorema: Complete Resolution (main result)
  - `conclusion.tex` - Conclusions and future work
  - `appendix_traces.tex` - Trace-Class Convergence proofs
  - `appendix_numerical.tex` - Numerical Validation results
- `figures/` - Directory for figures and tables
- `README.md` - This file with building instructions

## Quick Start

To build the complete RH paper:

```bash
cd docs/paper
pdflatex main.tex
pdflatex main.tex  # Run twice for cross-references and table of contents
```

## Compilation Instructions

### Standard LaTeX compilation:
```bash
pdflatex main.tex
pdflatex main.tex  # Second run resolves cross-references
```

### Alternative Compilation Methods

- **Using latexmk (recommended):**
  ```bash
  latexmk -pdf main.tex
  ```

- **Using make (if Makefile exists):**
  ```bash
  make
  ```

- **Using Overleaf:** Upload all `.tex` files and compile online

- **Using VS Code with LaTeX Workshop:** Open `main.tex` and use the LaTeX Workshop extension

## Package Dependencies

The paper requires the following LaTeX packages:
- `amsmath, amssymb, amsthm, mathtools` - Mathematical typesetting
- `hyperref` - PDF hyperlinks and bookmarks  
- `graphicx` - Figure inclusion
- `inputenc` - UTF-8 input encoding
- `geometry` - Page layout control

Most modern LaTeX distributions include these packages by default.

## Repository Integration

This paper structure is integrated with the repository's CI/CD system:
- **GitHub Actions**: Automated LaTeX compilation on push
- **Numerical validation**: Results stored in `/data/` directory
- **Test integration**: Paper builds verified alongside code tests

## Theorem Scaffolds

The paper incorporates formal theorem scaffolds covering:
- S-finite adelic spectral system axioms
- Archimedean rigidity and uniqueness results  
- de Branges theory application to RH
- Critical line localization via dual proof methods
- Complete trace-class convergence analysis

## Output

Successful compilation generates:
- `main.pdf` - The complete paper with all sections
- Auxiliary files (`.aux`, `.log`, `.out`, etc.) - automatically managed

## Troubleshooting

- **Missing packages:** Install via your LaTeX distribution (e.g., `tlmgr install packagename` for TeX Live)
- **Compilation errors:** Check the `.log` file for detailed error messages
- **Missing sections:** Ensure all `.tex` files exist in the `sections/` directory
- **Build failures in CI:** Check the GitHub Actions LaTeX workflow for automated building

## License

This work is licensed under CC-BY 4.0. See repository `LICENSE` file for details.

## Contact

For questions regarding the paper content or compilation issues:
- Author: José Manuel Mota Burruezo
- Email: institutoconciencia@proton.me
- GitHub: https://github.com/motanova84/-jmmotaburr-riemann-adelic
- Zenodo DOI: 10.5281/zenodo.17116291
