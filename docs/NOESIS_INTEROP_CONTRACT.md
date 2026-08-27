# NOESIS Interoperability Contract

## Canonical bridge

This repository is the spectral/adelic source node of the NOESIS ecosystem.

| Symbol | Canonical value | Role |
|---|---:|---|
| `f0` | `141.7001 Hz` | QCAL reference frequency |
| `fB` | `0.00052 Hz` | ultra-slow PHOENIX reference |
| `Psi_target` | `0.999999` | ecosystem coherence target |
| `alpha_inv` | `137.035999084` | fine-structure reference |

## Spectral interface

The logarithmic idelic coordinate `u = log|x|` turns multiplicative dilation into translation. The archimedean generator is represented by `D_inf = -i d/du`; finite places contribute arithmetic operators/multipliers. Downstream consumers MUST treat supplied Riemann ordinates as spectral input data, preserving provenance.

## Cross-node contract

`141hz` consumes this layer through `qcal/noesis_adelic_bio.py`. `field-qcal` consumes the resulting effective field sector. `RelojCuantico-141Hz-QCAL` provides the timing/reference layer. Biological/PHOENIX implementations consume `fB` as a signal-processing target.

The contract is dimensional: frequencies remain in Hz, angular frequencies in rad/s, and bridge ratios are dimensionless.

## Provenance

This document defines interoperability, not a claim that an implementation choice alone establishes a mathematical theorem. Computational results must retain their source repository, commit, parameters and test vector.
