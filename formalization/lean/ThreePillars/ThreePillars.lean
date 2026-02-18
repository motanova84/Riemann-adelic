/-
Copyright (c) 2026 José Manuel Mota Burruezo. All rights reserved.
Released under QCAL-SYMBIO-TRANSFER license.

# ThreePillars - Namespace Root

Este archivo establece el namespace raíz para los tres pilares
de la demostración de la Hipótesis de Riemann.

## Estructura:

- `ThreePillars.DomainSobolev`: PILAR 1 - Blindaje del dominio
- `ThreePillars.KatoSpectral`: PILAR 2 - Rigor espectral  
- `ThreePillars.PaleyWienerIdentity`: PILAR 3 - Identidad absoluta
- `ThreePillars.RiemannHypothesis`: Teorema final

## Uso:

```lean
import ThreePillars

open ThreePillars

theorem my_theorem : True := by
  have h := RiemannHypothesis.riemann_hypothesis
  trivial
```
-/

import ThreePillars.DomainSobolev
import ThreePillars.KatoSpectral
import ThreePillars.PaleyWienerIdentity
import ThreePillars.RiemannHypothesis
