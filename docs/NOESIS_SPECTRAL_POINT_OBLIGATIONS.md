# NOĒSIS — spectral-point and Schatten obligations

## Rigor checkpoint

The proposed conclusion that a trace-class perturbation of the dilation
operator automatically creates a pure point spectrum is **not valid in that
form**. Compactness of the perturbation does not remove the essential
spectrum of the unperturbed operator in general.

Likewise, the pure logarithmic shifts

\[
(T_a f)(t)=f(t+a)
\]

are unitary on `L²(R,dt)`. They are therefore not Hilbert–Schmidt or trace
class. A scalar series

\[
\sum_{p,m}|a_{p,m}|<\infty
\]

can establish operator-norm convergence of a sum of bounded shifts when the
individual operator norms are uniformly bounded, but it does **not** establish
Hilbert–Schmidt convergence.

## Consequence

The next valid construction must distinguish:

1. **bounded operator sum** — controlled by coefficient summability;
2. **compact perturbation** — requires an actual compactifying mechanism;
3. **Hilbert–Schmidt / trace class** — requires a kernel or singular-value
   estimate in the chosen Hilbert space;
4. **compact resolvent of `Dπ`** — is a separate theorem and cannot be inferred
   from (2) or (3) alone.

## Concrete next target

A mathematically viable candidate has to replace the pure translation sum by
something such as

\[
V=\sum_{p,m}a_{p,m}\,M_{w_{p,m}}T_{m\log p},
\]

or an equivalent adelic integral kernel, where the weights `w_{p,m}` provide
actual decay in both variables. Then one can attempt to prove

\[
\|V\|_{HS}^2
=\iint |K(t,u)|^2\,dt\,du<\infty,
\]

or a trace-class factorization `V=AB` with `A,B` Hilbert–Schmidt.

Only after this estimate is proved can a Schatten classification be claimed.

## Spectral-zero boundary

Even if a compact-resolvent self-adjoint operator is constructed, its real
spectrum does not by itself identify the zeros of ζ. The correspondence

\[
\operatorname{Spec}(D_\pi)\leftrightarrow
\{\gamma:\xi(1/2+i\gamma)=0\}
\]

remains an independent theorem.

This separation is essential: it prevents the spectral construction from
quietly importing the desired conclusion.
