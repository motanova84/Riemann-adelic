# Blueprint for Formal Verification (Lean/Isabelle)

## Goal
Provide a mechanically-checkable pathway for the RH program:
1) Entirety and order ≤ 1 of D(s)
2) Functional symmetry D(1-s) = D(s)
3) Archimedean factor (rigidity)
4) Positivity / self-adjoint operator (de Branges)
5) Final implication: all zeros on Re(s)=1/2

## Modules
- `entire_order.lean`: Hadamard factorization, growth bounds, Phragmén–Lindelöf
- `functional_eq.lean`: adelic Fourier, Poisson, normalization
- `arch_factor.lean`: Weil index ⇔ gamma factor
- `de_branges.lean`: HB function E, Hamiltonian H(x) ≻ 0, self-adjointness
- `positivity.lean`: Weil–Guinand quadratic form ≥ 0 on a dense class

## Milestones
- M1: compile stubs for (1)-(2)
- M2: formal lemma for Archimedean rigidity
- M3: positivity lemma in a simplified model (toy kernel)
- M4: integration of all modules into the RH statement skeleton

## Current status

Only scaffolding files exist; no Lean or Isabelle proofs have been implemented
yet.  Completing the milestones above is essential for Deliverables P4.1--P4.4
and for independent verification of the programme.
