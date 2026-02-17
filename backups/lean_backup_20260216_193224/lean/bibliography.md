# Bibliography

## References for Axioms to Lemmas Formalization

This bibliography contains the key references used in the formalization of the adelic framework axioms (A1, A2, A4) as lemmas in Lean 4.

### Primary References

**Tate, J.** (1967). *Fourier analysis in number fields and Hecke's zeta-functions*. In Algebraic Number Theory (Proc. Instructional Conf., Brighton, 1965), Thompson, Washington, D.C., pp. 305-347.
- **Relevance**: Foundation of adelic Fourier analysis and the adelic interpretation of L-functions. Essential for understanding the Schwartz-Bruhat functions on adeles and the Poisson summation formula in the adelic context.

**Weil, A.** (1964). *Sur certains groupes d'opérateurs unitaires*. Acta Mathematica, 111, 143-211.
- **Relevance**: Provides the theoretical foundation for unitary representations on adelic groups and the spectral theory underlying the flow operators. Key for understanding the adelic symmetry properties (Lemma A2).

**Birman, M. S. & Solomyak, M. Z.** (2003). *Double operator integrals in a Hilbert space*. Integral Equations and Operator Theory, 47(2), 131-168.
- **Relevance**: Essential for the trace-class theory and spectral bounds needed for the spectral regularity axiom (A4). Provides the mathematical framework for handling double operator integrals in the adelic setting.

**Simon, B.** (2005). *Trace Ideals and Their Applications*, 2nd edition. Mathematical Surveys and Monographs, Vol. 120, American Mathematical Society.
- **Relevance**: Comprehensive reference for trace class operators and their spectral properties. Fundamental for establishing the finite energy bounds (A1) and spectral regularity conditions (A4) in the adelic framework.

### Additional Context

These references form the mathematical foundation for:

1. **Lemma A1 (Finite Scale Flow)**: The finite energy bounds for adelic flow operators, based on the trace class theory from Simon and the adelic analysis from Tate.

2. **Lemma A2 (Poisson Adelic Symmetry)**: The functional equation D(1-s) = D(s), rooted in Weil's unitary representation theory and Tate's adelic Fourier analysis.

3. **Lemma A4 (Spectral Regularity)**: The analyticity and growth bounds for the canonical determinant D(s), utilizing the operator integral techniques of Birman-Solomyak and the spectral theory from Simon.

### Historical Note

The transition from axioms to lemmas represents a significant advancement in the rigor of the adelic approach to the Riemann Hypothesis. These references provide the theoretical foundations necessary for constructive proofs of what were previously assumed as axioms in the S-finite adelic framework.