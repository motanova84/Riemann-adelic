# Riemann-Adelic: Formal Proof Framework for the Riemann Hypothesis

[![CI](https://github.com/Ruthie-FRC/Riemann-adelic/actions/workflows/ci.yml/badge.svg)](https://github.com/Ruthie-FRC/Riemann-adelic/actions)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17379721.svg)](https://doi.org/10.5281/zenodo.17379721)
[![License: MIT](https://img.shields.io/badge/License--Code-MIT-blue.svg)](LICENSE-CODE)
[![License: CC BY 4.0](https://img.shields.io/badge/License--Manuscript-CC--BY--4.0-lightgrey.svg)](LICENSE)
[![Python 3.11+](https://img.shields.io/badge/Python-3.11%2B-green.svg)](https://www.python.org/)

A formal proof framework for the Riemann Hypothesis using S-finite adelic spectral systems. The approach constructs a self-adjoint operator H_Ψ whose spectrum coincides with the non-trivial zeros of the Riemann zeta function, then proves all eigenvalues lie on the critical line Re(s) = 1/2.

## Table of Contents

- [Overview](#overview)
- [Proof Structure](#proof-structure)
- [Repository Layout](#repository-layout)
- [Installation](#installation)
- [Running the Validation](#running-the-validation)
- [Lean 4 Formalization](#lean-4-formalization)
- [Documentation](#documentation)
- [Citation](#citation)
- [License](#license)

---

## Overview

This repository implements the QCAL (Quantum Coherent Adelic Lattice) framework, which encodes the Riemann Hypothesis as a spectral self-adjointness problem on an adelic Hilbert space. The proof proceeds in five verifiable steps:

1. **Axiom reduction** — Schwartz–Bruhat adelic setup forces the foundational axioms A1–A4 as theorems.
2. **Archimedean rigidity** — The archimedean factor is derived explicitly via the Weil index and stationary-phase analysis.
3. **Paley–Wiener uniqueness** — Compact adelic support forces D(s) into the Paley–Wiener class, giving a zeta-free construction.
4. **Zero localization** — The Berry–Keating operator H_Ψ is shown to be self-adjoint; its spectrum is identified with the non-trivial zeros.
5. **Coronación** — All non-trivial zeros are localized to Re(s) = 1/2.

The Lean 4 formalization lives in `formalization/lean/`. Python scripts in the root provide independent numerical validation.

---

## Proof Structure

```
Schwartz–Bruhat adelic setup
        │
        ▼
Axioms A1–A4  (derived as theorems, not assumed)
        │
        ▼
Archimedean factor  (stationary-phase derivation)
        │
        ▼
Paley–Wiener class  (compact support → unique analytic extension)
        │
        ▼
H_Ψ self-adjoint, Spec(H_Ψ) = {γₙ}  (Berry–Keating operator)
        │
        ▼
Re(ρ) = 1/2  for all non-trivial zeros  ∎
```

Key constants used throughout:
| Symbol | Value | Meaning |
|--------|-------|---------|
| f₀ | 141.7001 Hz | Base spectral frequency |
| C  | 244.36      | Coherence constant |
| κ_Π | 2.5773     | Geometric coupling invariant |

---

## Repository Layout

```
Riemann-adelic/
├── formalization/
│   ├── lean/          # Lean 4 proof files (180+ modules, 713+ theorems)
│   └── data/          # Machine-checkable certificates
├── docs/
│   ├── INDEX.md       # Documentation index
│   ├── roadmap/       # Development roadmap
│   ├── paper/         # LaTeX source for the accompanying paper
│   ├── formalizacion/ # Formalization blueprint
│   └── operators/     # Operator theory reference
├── tests/             # pytest test suite
├── zeros/             # Pre-computed Riemann zero data
├── data/              # Validation results and certificates
├── validate_v5_coronacion.py  # Main V5 validation script
├── riemann_spectral_5steps.py # 5-step spectral proof implementation
├── requirements.txt
└── pyproject.toml
```

---

## Installation

**Prerequisites:** Python 3.11 or higher, Git.

```bash
git clone https://github.com/Ruthie-FRC/Riemann-adelic.git
cd Riemann-adelic

# Create a virtual environment (recommended)
python3 -m venv venv
source venv/bin/activate   # Windows: venv\Scripts\activate

# Install dependencies
pip install -r requirements.txt
```

Optional: install pre-commit hooks for code-quality checks:
```bash
pip install pre-commit
pre-commit install
```

---

## Running the Validation

### Quick check (< 2 minutes)

```bash
python3 validate_v5_coronacion.py
```

Expected output:
```
✅ V5 CORONACIÓN — All validation checks passed
   Paley-Wiener uniqueness:  PASS
   Archimedean factor:       PASS
   Zero localization:        PASS
   Spectral identification:  PASS
```

### Full 5-step proof validation

```bash
python3 riemann_spectral_5steps.py
```

### Numerical Weil explicit formula (high precision)

```bash
python3 validate_explicit_formula.py \
    --use_weil_formula --max_zeros 200 --max_primes 200 \
    --precision_dps 30 --integration_t 50
```

### Run the test suite

```bash
pytest tests/ -v
```

---

## Lean 4 Formalization

The proof is formalized in Lean 4 using Mathlib 4. Key modules:

| Module | Content |
|--------|---------|
| `formalization/lean/RH_final.lean` | Top-level Riemann Hypothesis theorem |
| `formalization/lean/spectral/BerryKeating.lean` | H_Ψ self-adjointness |
| `formalization/lean/paley/PW_class_D_independent.lean` | Paley–Wiener uniqueness |
| `formalization/lean/RiemannAdelic/axioms_to_lemmas.lean` | Axiom derivation |
| `formalization/lean/spectral/Protocolo_MCC.lean` | Final zero localization |

To build the Lean project:
```bash
# Requires Lean 4 and Mathlib
lake build
```

See [`LEAN_SETUP_GUIDE.md`](LEAN_SETUP_GUIDE.md) for detailed setup instructions.

---

## Documentation

The [`docs/INDEX.md`](docs/INDEX.md) file provides a navigable index of all documentation in this repository, organized by topic:

- **Proof architecture** — `docs/roadmap/ROADMAP.md`, `IMPLEMENTATION_SUMMARY.md`
- **Mathematical background** — `docs/paper/`, `docs/teoremas_basicos/`
- **Operator theory** — `docs/operators/`
- **Validation guides** — `QUICKSTART.md`, `REPRODUCIBILITY.md`
- **Changelog** — `CHANGELOG.md`, `RELEASE_NOTES.md`
- **Contributing** — `CONTRIBUTING.md`
- **Security** — `SECURITY.md`

---

## Citation

If you use this work, please cite:

```bibtex
@software{mota_burruezo_2025_riemann,
  author    = {Mota Burruezo, José Manuel},
  title     = {Riemann–Adelic Proof Framework:
               Formal Verification of the Riemann Hypothesis},
  year      = {2025},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.17379721},
  url       = {https://doi.org/10.5281/zenodo.17379721}
}
```

See [`CITATION.cff`](CITATION.cff) for additional citation formats.

**Author:** José Manuel Mota Burruezo  
**ORCID:** [0009-0002-1923-0773](https://orcid.org/0009-0002-1923-0773)  
**Affiliation:** Instituto de Conciencia Cuántica (Institute for Quantum Consciousness research)  
**Contact:** institutoconsciencia@proton.me

---

## License

- **Code:** MIT License — see [`LICENSE-CODE`](LICENSE-CODE)
- **Manuscript / mathematical content:** CC BY 4.0 — see [`LICENSE`](LICENSE)

> **Note on GPU dependencies:** Core functionality runs on CPU only. Optional GPU acceleration via CuPy requires NVIDIA CUDA. See [`PACKAGE_LICENSES.md`](PACKAGE_LICENSES.md) for full dependency license details.
