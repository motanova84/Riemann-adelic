# NOĒSIS — explicit adelic potential and compact-resolvent program

## Rigor correction

The proposed statement that a trace-class perturbation of the free dilation operator automatically produces a compact resolvent is **not valid in general**.

If `R₀(z)` is non-compact and `V` is trace class, then

`R₀(z)V`

is trace class/compact, but this does **not** imply that

`R(z) = (z - (D₀ + V))⁻¹`

is compact. Compactness of the full resolvent must be proved independently, for example through a confining mechanism, a compact embedding of the operator domain, or another concrete spectral argument.

This correction is now part of the formal NOĒSIS proof boundary.

## Explicit construction target

Work initially with the multiplicative adelic Hilbert space

`H = L²(A_Q^× / Q^×, d×x)`

or a precisely equivalent unitary model. For each prime `p` and exponent `m ≥ 1`, define a prime-shift/Hecke action `T_{p^m}` independently of ζ-zeros.

The potential is intended to have the form

`V_adelic = Σ_{p,m} a_{p,m} T_{p^m}`

with coefficients whose exact normalization is derived from the adelic/Euler structure rather than chosen by spectral matching.

## Obligations

### A. Operator definition

1. Define the Hilbert space and Haar measure precisely.
2. Define the unitary Hecke/prime-shift operators.
3. Specify the coefficient sequence `a_{p,m}`.
4. Prove convergence in the required operator topology.
5. Prove symmetry/self-adjointness of the completed potential.

### B. Trace-class claim

A claim of trace class requires an actual Schatten estimate. In particular, a scalar bound on `|a_{p,m}|` is insufficient unless the operator norms and multiplicities of `T_{p^m}` are also controlled.

The formalization therefore records trace-class as an explicit obligation rather than assuming it from the factor `p^(-m/2)`.

### C. Compact resolvent

The desired theorem is

`(zI - D_π)⁻¹ ∈ S_∞(H)`

for one (hence all) `z` in the resolvent set, where `S_∞` denotes the compact operators.

This requires an independent proof. A trace-class perturbation only gives a compact difference of suitable resolvents under appropriate hypotheses; it does not convert a continuous-spectrum free operator into a compact-resolvent operator automatically.

### D. Spectral consequences

Only after self-adjointness and compact resolvent are established may we invoke the standard discrete-spectrum consequences: real eigenvalues of finite multiplicity and no finite accumulation point.

The determinant equation

`det(I - R₀(z)V_adelic) = 0`

is then a separate analytic correspondence statement. It is not a definition of the zeros of ζ.

## Frequency isolation

`141.7001 Hz` remains outside the mathematical construction until independently derived. This prevents the operator from being tuned to a desired numerical output.

## Next theorem

The next concrete target is therefore:

> Construct `T_{p^m}` and `V_adelic` on a specified Hilbert space and prove a genuine operator-topology convergence theorem.

After that, attack compactness of the full resolvent by a mechanism that is independent of the trace-class perturbation argument.
