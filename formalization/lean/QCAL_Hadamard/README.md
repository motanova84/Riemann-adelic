# QCAL Hadamard uniqueness (fuente)

Enunciado:

enteras \(f,g\), orden \(\le 1\) (`OrderAtMostOne`), mismos ceros con multiplicidad,
\(f(1-s)=f(s)\), \(g(1-s)=g(s)\), \(f(1/2)=g(1/2)\ne 0\) \(\Rightarrow\) \(f=g\).

Teorema: `hadamard_uniqueness` en `QCAL_Hadamard_Huecos_Nombrados_v3.2.5.lean`.

GAP1 log holomorfo · GAP2 Borel + Cauchy n=2 · GAP3 Riemann extraíble ·
GAP4 min |g| en círculo separado y `OrderAtMostOne` del cociente.

## Qué no es

No es RH. No es \(D\equiv\Xi\). No es Paley–Wiener para \(\xi\).
No está lake-checked hasta que `lake build` cierre en este directorio.

## Build (sin `lake update`)

```bash
cd formalization/lean/QCAL_Hadamard
lake build
```

Toolchain: Lean 4.32.1. Mathlib pin `v4.32.1` en `lakefile.lean`.
No `lake update`. No bump de mathlib.

José Manuel Mota Burruezo · Noesis · QCAL ∞³
