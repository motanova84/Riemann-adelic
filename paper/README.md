# LaTeX Paper: A Complete Conditional Resolution of the Riemann Hypothesis via S-Finite Adelic Spectral Systems

## Overview

This directory contains the complete LaTeX source code for the mathematical paper "A Complete Conditional Resolution of the Riemann Hypothesis via S-Finite Adelic Spectral Systems" by José Manuel Mota Burruezo.

## File Structure

- `main.tex` - Main LaTeX file with document structure and bibliography
- `section1.tex` - Axiomatic Scale Flow and Spectral System
- `section2.tex` - Construction of the Canonical Determinant D(s)
- `section3.tex` - Trace Formula and Geometric Emergence of Logarithmic Lengths
- `section4.tex` - Asymptotic Normalization and Hadamard Identification
- `appendix_a.tex` - Paley–Wiener Uniqueness with Multiplicities
- `appendix_b.tex` - Archimedean Term via Operator Calculus
- `appendix_c.tex` - Uniform Bounds and Spectral Stability
- `figures/` - Directory for figures and tables
- `requirements.txt` - LaTeX package dependencies
- `LICENSE` - CC-BY 4.0 license

## Compilation Instructions

### Prerequisites

Ensure you have a complete LaTeX distribution installed:

- **TeX Live** (Linux/Windows) or **MacTeX** (macOS)
- **pdflatex** compiler
- Required LaTeX packages (see requirements.txt)

### Compilation Steps

1. **Standard compilation:**
   ```bash
   pdflatex main.tex
   pdflatex main.tex  # Run twice for cross-references
   ```

2. **With bibliography (if using BibTeX):**
   ```bash
   pdflatex main.tex
   bibtex main
   pdflatex main.tex
   pdflatex main.tex
   ```

3. **Complete build with all references:**
   ```bash
   pdflatex main.tex
   bibtex main
   pdflatex main.tex
   pdflatex main.tex
   ```

### Alternative Compilation Methods

- **Using latexmk (recommended):**
  ```bash
  latexmk -pdf main.tex
  ```

- **Using Overleaf:** Upload all `.tex` files and compile online

- **Using VS Code with LaTeX Workshop:** Open `main.tex` and use the LaTeX Workshop extension

## Package Dependencies

The paper requires the following LaTeX packages:
- `amsmath, amssymb, amsthm` - Mathematical typesetting
- `hyperref` - PDF hyperlinks and bookmarks  
- `graphicx` - Figure inclusion
- `inputenc` - UTF-8 input encoding

Most modern LaTeX distributions include these packages by default.

## Figures

The `figures/` directory contains placeholder files for:
- `delta_eta.pdf` - Plot of the function Δ(η)
- `table_errors.pdf` - Error analysis table

**Note:** Replace placeholder files with actual figures before final compilation.

## Output

Successful compilation generates:
- `main.pdf` - The complete paper
- Auxiliary files (`.aux`, `.log`, `.out`, etc.) - automatically managed

## Troubleshooting

**Common issues:**

1. **Missing packages:** Install via package manager (`tlmgr install <package>`)
2. **Bibliography errors:** Ensure all citations have corresponding entries
3. **Figure errors:** Check that figure files exist in the `figures/` directory
4. **Cross-reference errors:** Run pdflatex multiple times

**Clean build:**
```bash
rm -f *.aux *.log *.out *.toc *.bbl *.blg
pdflatex main.tex
```

## License

This work is licensed under the Creative Commons Attribution 4.0 International License (CC-BY 4.0). See the LICENSE file for details.

## Contact

For questions about the mathematical content, contact:
- José Manuel Mota Burruezo: institutoconciencia@proton.me
- GitHub repository: https://github.com/motanova84/-jmmotaburr-riemann-adelic