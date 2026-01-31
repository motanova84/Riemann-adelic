/-!
# Hilbert-Pólya Proof of the Riemann Hypothesis

This library formalizes the operator-theoretic proof of the Riemann Hypothesis
via the Hilbert-Pólya approach.

## Structure

1. `KernelExplicit`: Explicit kernel K(x,y) and Hilbert-Schmidt property
2. `CompactResolvent`: Compact resolvent and discrete spectrum
3. `GuinandWeil`: Trace formula and spectral-zeta bijection
4. `RHProved`: Main proof of the Riemann Hypothesis
5. `NoesisInfinity`: Noēsis ∞³ verification system
6. `Main`: Complete system integration

## Main Result

`Hilbert_Polya_System_Complete`: The complete verification that the Riemann
Hypothesis follows from the spectral properties of the operator H_ψ.

-/

import HilbertPolyaProof.KernelExplicit
import HilbertPolyaProof.CompactResolvent
import HilbertPolyaProof.GuinandWeil
import HilbertPolyaProof.RHProved
import HilbertPolyaProof.NoesisInfinity
import HilbertPolyaProof.Main
