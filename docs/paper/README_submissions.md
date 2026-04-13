# Submission README

## Summary
- **Manuscript:** `main.tex` (compiled as `main.pdf` / artifact `rh-paper.pdf`).
- **Scope:** Derives axioms A1--A4 from standard adelic theory, proves Archimedean rigidity, establishes Paley--Wiener--Hamburger uniqueness, and combines de Branges and Weil--Guinand positivity to force critical-line zeros.
- **Supplementary:** Proof-check scripts under `proof-check/` with automated `pytest` execution.

## Divergence from prior work
- Avoids reliance on the Euler product by operating purely with adelic Fourier transforms and Weil indices.
- Uses Birman--Solomyak trace theory to control spectral regularity instead of assuming it.
- Merges de Branges canonical systems with Weil--Guinand positivity in a single framework to reach the critical line.

## Reproducibility
1. Install dependencies: `pip install -r requirements.txt` (or rely on CI workflow for reference).
2. Build the paper locally:
   ```bash
   cd docs/paper
   pdflatex main.tex
   bibtex main
   pdflatex main.tex
   pdflatex main.tex
   ```
3. Run proof checks:
   ```bash
   pytest -q
   ```

## Target venues and arXiv plan
- Primary targets: *Journal d'Analyse Mathématique*, *International Mathematics Research Notices*, *Advances in Mathematics*.
- Prepare an arXiv submission in tandem, using `main.pdf` and `cover_letter.md` as supporting documents.

## Next steps before submission
- Expand the analytic estimates flagged in the conclusion's “Status and limitations”.
- Translate the blueprint in `formalization/lean/` into checked proofs.
- Collect referee-facing logs from CI runs (available under GitHub Actions artifacts).
