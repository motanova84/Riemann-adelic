# NOĒSIS — confinement architecture, rigor checkpoint v9.1

## What is established by the proposed Gaussian envelope

A kernel of the form

\[
K_N(t,u)=e^{-\beta(t^2+u^2)}\sum_{n<N}c_n
 e^{-\beta(u-t-a_n)^2},\qquad \beta>0,
\]

is an ordinary measurable function rather than a sum of delta distributions.
For finite `N`, its Gaussian factors provide the route to an explicit
Hilbert–Schmidt estimate.

## Two corrections that remain essential

### 1. Delta kernels are not Hilbert–Schmidt

A translated delta kernel `δ(u-t-a)` is supported on a measure-zero diagonal
and is not an `L²(R²)` function. Therefore the original delta-translation
argument cannot be used as an HS proof. The Gaussian replacement fixes this
specific issue.

### 2. Hilbert–Schmidt is not trace class

\[
\mathcal L^1\subsetneq\mathcal L^2.
\]

Thus `V ∈ L²` does not imply `V ∈ L¹`. A separate nuclear/factorisation estimate
is required. In particular, the formal factorisation `V=V^{1/2}V^{1/2}` is
not sufficient unless `V` is positive trace class (or the relevant square-root
membership has itself been proved).

### 3. Compact perturbation does not create compact resolvent

If the free dilation generator has non-compact resolvent, adding a bounded
compact or trace-class perturbation does not automatically make the new
resolvent compact. The compact-resolvent proof must instead establish a genuine
confining mechanism, typically through a coercive quadratic form and a compact
embedding of the associated form domain.

## Correct target theorem

The next rigorous target is therefore:

1. define the self-adjoint free operator and its domain;
2. define the confined potential as an explicit measurable kernel/multiplication
   operator;
3. prove symmetry and self-adjointness of the full operator;
4. establish coercivity of its quadratic form;
5. prove compact embedding of the form domain into the Hilbert space;
6. deduce compact resolvent;
7. only then derive discreteness and finite multiplicity of eigenvalues;
8. independently prove the Fredholm/Weil identity;
9. independently prove the spectral correspondence with `ξ`.

No zero of ζ is used in the construction of the confined operator.

## Status

This checkpoint is **not** a proof of RH and does not assert that the proposed
Gaussian confinement has already been shown to reproduce the Riemann explicit
formula. It records the exact analytic obligations required to get there.
