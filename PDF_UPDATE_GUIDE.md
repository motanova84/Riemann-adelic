# PDF Documentation Guidelines: Axioms to Theorems

## Overview

This guide explains how to update the PDF manuscript (`paper/main.tex`) to replace axiom-based formulations with theorem-based formulations, following the V5.3.1 axiom purge.

## Key Changes Required

### 1. Replace "Axioma" Labels with "Teorema" Labels

**Current Structure** (V5.2 and earlier):
- References to "Axioma A1", "Axioma A2", "Axioma A4"
- Axioms presented as foundational assumptions

**New Structure** (V5.3.1+):
- Replace with "Teorema 5.7" (D ≡ Ξ), "Teorema 6.3" (Critical Line), "Lema 4.2" (Trivial Zeros)
- Present as proven results with proof sketches

### 2. Three Main Theorems

#### Teorema 5.7 (D ≡ Ξ)

**Enunciado**: Sea D entera de orden ≤1 con D(1-s) = D(s), D(σ+it) → 1 cuando σ → +∞, y cuyo divisor coincide con el de ζ en 0 < ℜs < 1 (excluidos los ceros triviales). Entonces D ≡ Ξ.

**Esquema de prueba**:
1. Factorización de Hadamard para D y Ξ
2. Cociente Q = D/Ξ es entero, sin ceros, orden ≤1, y Q(σ+it) → 1 cuando σ → +∞
3. Clase de determinantes relativos + Paley-Wiener (Koosis-Young): control subgaussiano global ⇒ Q acotada entera ⇒ constante
4. Normalización en un punto fijo del semiplano derecho ⇒ Q ≡ 1. Concluye D ≡ Ξ. □

**Lean Formalization**: `formalization/lean/RiemannAdelic/axiom_purge.lean`, theorem `D_eq_Xi`

**References**:
- Hadamard (1893): Factorization theory
- Paley-Wiener (1934): Uniqueness theorems
- Koosis (1988): The Logarithmic Integral
- Young (2001): An Introduction to Nonharmonic Fourier Series

#### Teorema 6.3 (Ceros en la línea crítica)

**Enunciado**: Existe un operador autoadjunto H (módulo cociente) cuyo espectro es {ℑρ} para ρ ceros no triviales de D. Con la simetría funcional y positividad del kernel explícito se fuerza ℜρ = 1/2.

**Idea clave**: Forma bilineal coerciva del kernel explícito (tipo Weil) en el cociente; autoadjunción ⇒ espectro real; simetría funcional + patrón de signos ⇒ confinamiento a ℜs = 1/2. □

**Lean Formalization**: `formalization/lean/RiemannAdelic/axiom_purge.lean`, theorem `all_zeros_on_critical_line`

**References**:
- de Branges (1968): Hilbert spaces of entire functions
- Weil (1952): Sur les "formules explicites" de la théorie des nombres premiers
- Birman-Solomyak (2003): Spectral theory of self-adjoint operators

#### Lema 4.2 (Exclusión de ceros triviales)

**Enunciado**: Separación vía el factor gamma archimediano: los ceros triviales de ζ son absorbidos en el Γ-producto; el divisor adoptado por D en la banda crítica no los incluye. □

**Lean Formalization**: `formalization/lean/RiemannAdelic/axiom_purge.lean`, lemma `trivial_zeros_excluded`

**References**:
- Riemann (1859): Über die Anzahl der Primzahlen
- Tate (1950): Fourier analysis in number fields

### 3. Hypotheses U1/U2

The proofs depend on uniform convergence and subgaussian control. These should be explicitly labeled as numbered hypotheses throughout the document.

#### Hipótesis U1 (Convergencia uniforme)

**Statement**: La traza espectral D(s) converge uniformemente en conjuntos compactos de la banda crítica, permitiendo intercambio de límites.

**Justification**: Follows from Schwartz-Bruhat theory on adeles and trace-class operator properties (Birman-Solomyak).

**Used in**: Steps (i) and (ii) of Theorem 5.7

#### Hipótesis U2 (Control subgaussiano)

**Statement**: El crecimiento de D(s) satisface estimaciones subgaussianas globales: |D(σ+it)| ≤ C exp(c|t|^α) con α < 1.

**Justification**: Follows from entire function order ≤1 and Hadamard factorization with convergent product.

**Used in**: Step (iii) of Theorem 5.7 (Paley-Wiener determinacy)

### 4. Editorial Notes

#### Normalization as Corollary

The normalization D(1/2) = Ξ(1/2) should be moved from the main theorems to a corollary:

**Corolario 5.8 (Normalización canónica)**: 
Bajo las condiciones del Teorema 5.7, la normalización D(1/2) = Ξ(1/2) determina unívocamente Q ≡ 1.

**Proof**: By Liouville's theorem, Q is constant. Evaluating at s = 1/2 gives Q(1/2) = D(1/2)/Ξ(1/2) = 1 by normalization. Hence Q ≡ 1. □

Do **not** call this "calibración" as it might suggest an arbitrary choice rather than a canonical normalization.

#### Separate Statement from Interpretation

Structure each section as:

1. **Statement** (Enunciado): Mathematical theorem/lemma with precise conditions
2. **Proof Sketch** (Esquema de prueba): High-level logical steps
3. **Interpretation** (Interpretación noésica): Optional philosophical/conceptual discussion

This separation ensures mathematical rigor is not conflated with conceptual interpretation.

## File Locations for Updates

### Main Files
- `paper/main.tex`: Main document, update references to axioms
- `paper/section1b.tex`: "From Axioms to Lemmas" section, update to reflect theorem status
- `paper/section4.tex`: Update Hadamard identification section with Theorem 5.7
- `paper/section5.tex`: Update with Theorem 6.3 (if exists)
- `paper/section6.tex`: Update with Lema 4.2 (if exists)

### Spanish Coronación Section
- `docs/teoremas_basicos/coronacion_v5.tex`: Spanish version of V5 completion, update axiom references

## Bibliography Configuration (Future)

To enable biblatex (recommended for better citation management):

### In `paper/main.tex` preamble:
```latex
\usepackage[backend=biber,style=alphabetic,maxbibnames=99]{biblatex}
\addbibresource{refs.bib}
```

### Replace `\begin{thebibliography}...\end{thebibliography}` with:
```latex
\printbibliography
```

### Create `paper/refs.bib`:
```bibtex
@article{hadamard1893,
  author = {Hadamard, Jacques},
  title = {Étude sur les propriétés des fonctions entières et en particulier d'une fonction considérée par Riemann},
  journal = {Journal de Mathématiques Pures et Appliquées},
  year = {1893},
  volume = {9},
  pages = {171--215}
}

@book{paley1934,
  author = {Paley, Raymond E. A. C. and Wiener, Norbert},
  title = {Fourier Transforms in the Complex Domain},
  publisher = {American Mathematical Society},
  year = {1934},
  series = {Colloquium Publications},
  volume = {19}
}

% Add more entries...
```

## Compilation Instructions

With biblatex enabled:
```bash
cd paper
pdflatex main.tex
biber main
pdflatex main.tex
pdflatex main.tex
```

Or use `latexmk` (automated):
```bash
cd paper
latexmk -pdf -shell-escape main.tex
```

Or use the Makefile:
```bash
make pdf
```

## Checklist for PDF Updates

- [ ] Replace all "Axioma A1", "Axioma A2", "Axioma A4" with appropriate theorem/lemma references
- [ ] Add Theorem 5.7 (D ≡ Ξ) with full statement and proof sketch
- [ ] Add Theorem 6.3 (Critical Line) with full statement and proof sketch
- [ ] Add Lema 4.2 (Trivial Zeros) with full statement
- [ ] Label U1 and U2 as "Hipótesis U1" and "Hipótesis U2" with explicit statements
- [ ] Move normalization to Corollary 5.8
- [ ] Separate "Statement" from "Interpretation" in each theorem
- [ ] Update cross-references to point to new theorem numbers
- [ ] Add footnotes linking to Lean formalization: `formalization/lean/RiemannAdelic/axiom_purge.lean`
- [ ] Verify all citations have proper bibliography entries (current or future biblatex)
- [ ] Test compilation with `make pdf` or `latexmk`

## Version Control

After updates:
```bash
git add paper/main.tex paper/section*.tex
git commit -m "Update PDF: axioms to theorems per V5.3.1"
git push
```

---

**Maintained by**: José Manuel Mota Burruezo (@motanova84)  
**Version**: 5.3.1  
**Date**: 2025-10-30  
**Status**: Guidelines established, implementation pending
