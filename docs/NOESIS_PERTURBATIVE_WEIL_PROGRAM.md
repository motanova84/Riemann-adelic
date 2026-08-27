# NOĒSIS — perturbative derivation of the Weil explicit formula

## Status

This document formalizes the **proof program and dependency boundaries** for the proposed adelic perturbation argument. It is not presented as a completed proof of the Riemann Hypothesis.

The central requirement is non-circularity: the construction of the operator and perturbation must be independent of the non-trivial zeros of `ζ`.

## 1. Target operator

Let

\[
\mathcal H=L^2(\mathbb R_+,dx/x),
\qquad
D_0=-i\,x\frac{d}{dx}
\]

on an explicitly specified dense core. The existing dilation generator has continuous spectrum, so the next construction must specify a genuine perturbation

\[
D_\pi=D_0+V_{\rm adelic}
\]

and prove, rather than assume, the spectral properties needed below.

### Required obligations

1. `D0` is symmetric on the stated core.
2. The chosen closure/self-adjoint extension is mathematically justified.
3. `V_adelic` is a well-defined symmetric operator (or bounded/self-adjoint perturbation under stated hypotheses).
4. `Dπ` is self-adjoint on an explicit domain.
5. The relevant resolvent is compact if a discrete spectrum is claimed.

No zero of `ζ` may occur in the definition of any item in this list.

## 2. Resolvent identity

For `z` in the common resolvent set,

\[
R_0(z)=(zI-D_0)^{-1},\qquad
R(z)=(zI-D_\pi)^{-1}.
\]

The exact resolvent identity is

\[
R(z)-R_0(z)=R(z)V_{\rm adelic}R_0(z),
\]

with the appropriate sign convention fixed by the definition of the resolvent. Trace-class hypotheses must be stated before taking traces.

The Lean bridge in
`formalization/lean/RiemannAdelic/Noesis/NonCircularWeil.lean`
separates this algebraic identity from the analytic work required to instantiate it.

## 3. Prime-side perturbation

The proposed kernel must be defined independently of the zeros and then shown to generate the prime-power weights appearing in the explicit formula. The target structure is

\[
\sum_{p}\sum_{m\ge1}
(\log p)\,p^{-m/2}\,\widehat h(m\log p),
\]

up to the exact normalization dictated by the chosen Fourier/Mellin convention.

This normalization must be derived, not selected to match the target formula.

## 4. Fredholm determinant route

For a trace-class operator `K`, the Fredholm determinant satisfies

\[
\log\det(I+K)
=
\sum_{n\ge1}\frac{(-1)^{n-1}}n\operatorname{Tr}(K^n),
\]

under the convergence hypotheses of the chosen determinant class.

The required NOĒSIS theorem is therefore a chain:

\[
V_{\rm adelic}
\longrightarrow
\operatorname{Tr}(K^n)
\longrightarrow
\log\det(I+K)
\longrightarrow
\text{prime-power distribution}.
\]

The equality with the completed zeta function must be proved independently; it cannot be inserted as a definition of `K`.

## 5. Weil trace formula

For an admissible test function `h`, the target identity has the schematic form

\[
\sum_{\rho}h(\gamma_\rho)
=
\text{archimedean contribution}
-
\sum_{p,m}
\frac{\log p}{p^{m/2}}\,g(m\log p),
\]

with the precise convention for `g`, `h`, the trivial-zero terms, and the pole term fixed explicitly.

The equality must be obtained in two independently justified ways:

- spectral evaluation of the trace/determinant;
- prime/archimedean evaluation from the adelic perturbation.

Only after both sides are established can they be identified.

## 6. Separation of the RH step

The spectral-zero correspondence is a separate theorem:

\[
\operatorname{Spec}(D_\pi)
\longleftrightarrow
\{\gamma:\nobreak\xi(1/2+i\gamma)=0\}.
\]

It must not be part of the construction of `Dπ`.

If the correspondence is eventually proved and `Dπ` is self-adjoint, then its spectral parameters are real. The remaining normalization theorem must show that the associated zero has the form

\[
\rho=\frac12+i\gamma.
\]

Self-adjointness alone does **not** establish this correspondence.

## 7. Frequency isolation

`f0 = 141.7001 Hz` is kept outside the mathematical construction until an independent derivation exists. It may be recorded as an experimental/reference parameter, but it must not be inserted into the operator, perturbation, determinant, or zero correspondence merely to force agreement.

This creates a machine-checkable dependency rule:

\[
f_0\notin\operatorname{Deps}(D_0,V_{\rm adelic},D_\pi)
\]

before the independent prediction/identification theorem.

## 8. Completion ladder

The implementation proceeds in this order:

1. **Hilbert-space/domain layer** — explicit analytic definitions.
2. **Self-adjointness layer** — closure/extension theorem.
3. **Perturbation layer** — explicit prime-side kernel.
4. **Compact-resolvent layer** — proof of discreteness where claimed.
5. **Trace-class layer** — nuclearity and convergence bounds.
6. **Fredholm layer** — determinant and logarithmic derivative.
7. **Weil layer** — exact explicit formula with all correction terms.
8. **Spectral correspondence layer** — independent correspondence with zeros.
9. **RH corollary** — only after 1–8 are proved.

At every stage, a failed obligation remains a failed obligation; comments, numerical agreement, or a pre-existing zero list do not discharge it.
