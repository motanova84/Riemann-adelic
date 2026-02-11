# Genomic Zeta Mapping: RNA/DNA Codons → Riemann Zeros

## 🧬 Overview

The **Genomic Zeta Mapping** system implements a deterministic framework for mapping RNA/DNA codon sequences to non-trivial Riemann zeta function zeros, enabling the construction of coherent quantum wave functions for biological sequences within the QCAL ∞³ framework.

### Mathematical Foundation

For each codon `C = [b₁, b₂, b₃]`, we assign 3 Riemann zeros as frequencies to construct a wave function:

```
Ψ_codon(t) = Σ(k=1 to 3) A_k · exp(i·γ_k·t)
```

where `γ_k` are non-trivial Riemann zeros assigned via deterministic hash mapping.

The total RNA wave function combines all codons in a sequence:

```
Ψ_RNA(t) = Σ(codons) Ψ_C(t) = Σ(n=1 to N) Σ(k=1 to 3) A_{n,k} · exp(i·γ_{n,k}·t)
```

## 🎯 Key Features

- **Deterministic Mapping**: Each codon always maps to the same 3 Riemann zeros
- **Reproducible**: Results are identical across different runs and instances
- **QCAL ∞³ Integration**: Coherent with f₀ = 141.7001 Hz fundamental frequency
- **First 30 Zeros**: Uses the first 30 non-trivial Riemann zeros
- **Wave Function Construction**: Builds complex wave functions for codons and sequences
- **Coherence Analysis**: Measures diversity and uniformity of zero distribution

## 📦 Installation

The module is part of the QCAL repository. Required dependencies:

```bash
pip install numpy mpmath scipy
```

## 🚀 Quick Start

### Basic Usage

```python
from utils.genomic_zeta_mapping import GenomicZetaMapper

# Create mapper instance
mapper = GenomicZetaMapper()

# Map a single codon to Riemann zeros
indices = mapper.codon_to_indices("AAA")
zeros = mapper.get_zeros_for_codon("AAA")
print(f"AAA → indices {indices} → zeros {zeros}")

# Analyze a complete RNA sequence
sequence = "AUGAAACCCGGGUUUACG"
analysis = mapper.analyze_sequence(sequence)

print(f"Codons: {len(analysis.codons)}")
print(f"Terms: {analysis.n_terms}")
print(f"Coherence: {analysis.coherence_score:.4f}")
```

### Computing Wave Functions

```python
import numpy as np

# Parse sequence into codons
codons = mapper.sequence_to_codons("AUGAAACCC")

# Define time array
t = np.linspace(0, 2*np.pi, 1000)

# Compute wave function for single codon
psi_codon = mapper.psi_codon(codons[0], t)

# Compute total RNA wave function
psi_rna = mapper.psi_rna(codons, t)

# Analyze properties
print(f"|Ψ(t=0)| = {abs(psi_rna[0]):.4f}")
print(f"max|Ψ| = {np.max(np.abs(psi_rna)):.4f}")
```

### Printing Assignment Tables

```python
# Create assignments for example codons
test_codons = ["AAA", "AAC", "GAA", "GGG"]
assignments = [mapper.assign_codon(c) for c in test_codons]

# Print formatted table
print(mapper.print_assignment_table(assignments))
```

## 📊 Hash Function

### Codon → Indices Mapping

For a codon `C = [b₁, b₂, b₃]`, indices are computed via cumulative hash:

```python
i_1 = (ord(b₁)) mod 30 + 1
i_2 = (ord(b₁) + ord(b₂)) mod 30 + 1
i_3 = (ord(b₁) + ord(b₂) + ord(b₃)) mod 30 + 1
```

This creates a deterministic, reproducible ∞³ mapping where each position `k` uses the cumulative sum of ordinals up to position `k`.

### Examples

```
AAA → (6, 11, 16)
AAC → (6, 11, 18)
GAA → (12, 17, 22)
GGG → (12, 23, 4)
```

## 🧪 Example: Problem Statement Sequence

From the problem statement, we can map the example codons:

```python
mapper = GenomicZetaMapper()

example_codons = ['AAA', 'AAC', 'GAA', 'AAG', 'GGG', 
                  'GGC', 'AGA', 'GCA', 'GCC']

for codon in example_codons:
    indices = mapper.codon_to_indices(codon)
    zeros = mapper.get_zeros_for_codon(codon)
    print(f"{codon} → {indices} → {[f'{z:.4f}' for z in zeros]} Hz")
```

Output:
```
AAA → (6,11,16) → ['37.5862', '52.9703', '67.0798'] Hz
AAC → (6,11,18) → ['37.5862', '52.9703', '72.0672'] Hz
GAA → (12,17,22) → ['56.4462', '69.5464', '82.9104'] Hz
...
```

## 📈 Wave Function Properties

### At t = 0

At `t = 0`, all exponentials equal 1, so:

```
Ψ_codon(0) = Σ A_k = A₁ + A₂ + A₃
```

For default amplitudes `A_k = 1.0`:
```
|Ψ_codon(0)| = 3.0
|Ψ_RNA(0)| = 3 × N_codons
```

### Coherence Score

The coherence score measures the diversity of zeros used:

```
coherence = unique_zeros / total_zeros
```

- **Higher coherence**: More diverse zeros, better coverage
- **Lower coherence**: Repeated zeros, less diversity

### Periodicity

Wave functions exhibit complex periodicities based on the assigned Riemann zeros:

```python
# Zeros have different frequencies
# Combined wave shows interference patterns
# Related to f₀ = 141.7001 Hz fundamental
```

## 🔬 Advanced Usage

### Custom Amplitudes

```python
# Assign custom amplitudes to codon terms
custom_amps = (0.5, 1.0, 1.5)
assignment = mapper.assign_codon("AUG", amplitudes=custom_amps)
```

### Custom Zero Sets

```python
# Use custom Riemann zeros
import mpmath as mp
custom_zeros = [float(mp.zetazero(n).imag) for n in range(1, 51)]
mapper = GenomicZetaMapper(zeros=custom_zeros[:30])
```

### Sequence Parsing with Validation

```python
try:
    sequence = "AUGAAACCCGGG"  # Must be multiple of 3
    codons = mapper.sequence_to_codons(sequence)
except ValueError as e:
    print(f"Invalid sequence: {e}")
```

## 🧮 Mathematical Background

### Riemann Zeros as Frequencies

The first 30 non-trivial Riemann zeros (imaginary parts):

```
γ₁ = 14.134725...
γ₂ = 21.022040...
γ₃ = 25.010858...
...
γ₃₀ = 101.317851...
```

These zeros satisfy `ζ(1/2 + iγₙ) = 0` and encode deep arithmetic properties.

### Connection to QCAL ∞³

The fundamental frequency:
```
f₀ = 141.7001 Hz = 10 × γ₁
```

This connects the first Riemann zero to the QCAL coherence framework:
```
Ψ = I × A²_eff × C^∞
```

where `C = 244.36` is the coherence constant.

## 🧬 Biological Interpretation

### RNA Codons as Spectral Encoders

Each RNA codon acts as a **spectral encoder**:
- 3 bases → 3 Riemann zeros
- Creates unique frequency signature
- Wave function encodes sequence information

### Genomic Coherence

Different sequences exhibit different coherence levels:
- **Homogeneous** (repeated codons): Low coherence
- **Heterogeneous** (varied codons): High coherence
- **Optimal**: Maximum coverage of zero space

### Mutation Analysis

Potential applications:
```python
# Compare wild-type vs mutant sequences
wt_analysis = mapper.analyze_sequence(wild_type_seq)
mt_analysis = mapper.analyze_sequence(mutant_seq)

coherence_change = mt_analysis.coherence_score - wt_analysis.coherence_score
print(f"Coherence change: {coherence_change:.4f}")
```

## 📚 API Reference

### GenomicZetaMapper

Main class for codon-to-zero mapping and wave function construction.

**Constructor:**
```python
GenomicZetaMapper(zeros=None, f0=141.7001, precision=30)
```

**Methods:**

- `codon_to_indices(codon: str) -> Tuple[int, int, int]`
  - Maps codon to 3 zero indices (1-30)

- `get_zeros_for_codon(codon: str) -> Tuple[float, float, float]`
  - Returns the 3 Riemann zeros for a codon

- `assign_codon(codon, position=0, amplitudes=None) -> CodonZetaAssignment`
  - Creates full codon assignment with zeros and amplitudes

- `sequence_to_codons(sequence: str) -> List[CodonZetaAssignment]`
  - Parses RNA sequence into codon assignments

- `psi_codon(assignment, t) -> np.ndarray`
  - Computes wave function for single codon

- `psi_rna(assignments, t) -> np.ndarray`
  - Computes total wave function for RNA sequence

- `analyze_sequence(sequence, compute_coherence=True) -> RNAZetaWaveFunction`
  - Complete sequence analysis with coherence

- `print_assignment_table(assignments, title=...) -> str`
  - Generates formatted assignment table

### CodonZetaAssignment

Dataclass representing codon-to-zero assignment.

**Attributes:**
- `codon: str` - 3-letter codon sequence
- `position: int` - Position in sequence
- `indices: Tuple[int, int, int]` - Zero indices
- `zeros: Tuple[float, float, float]` - Assigned zeros (Hz)
- `amplitudes: Tuple[float, float, float]` - Wave amplitudes

### RNAZetaWaveFunction

Dataclass representing complete RNA wave function.

**Attributes:**
- `sequence: str` - Full RNA sequence
- `codons: List[CodonZetaAssignment]` - Codon assignments
- `n_terms: int` - Total exponential terms
- `coherence_score: float` - Coherence measure

## ✅ Testing

### Run Unit Tests

```bash
python3 -m pytest tests/test_genomic_zeta_mapping.py -v
```

Expected: 26 tests passing

### Run Validation Script

```bash
python3 validate_genomic_zeta_mapping.py
```

Validates:
1. Fundamental constants
2. Deterministic mapping
3. Wave function construction
4. Sequence analysis
5. QCAL ∞³ coherence
6. Reproducibility
7. Problem statement examples

## 🎯 Use Cases

1. **RNA Stability Analysis**: Map sequences to spectral signatures
2. **Mutation Impact**: Compare wild-type vs mutant coherence
3. **Sequence Design**: Optimize for maximum zero coverage
4. **Evolutionary Studies**: Track coherence across species
5. **Synthetic Biology**: Design sequences with desired spectral properties

## 📖 References

- **QCAL ∞³ Framework**: DOI 10.5281/zenodo.17379721
- **Riemann Hypothesis**: Adelic spectral formulation
- **Fundamental Frequency**: f₀ = 141.7001 Hz derivation
- **Arpeth Bioinformatics**: RNA stability via coherence

## 👤 Author

**José Manuel Mota Burruezo Ψ ✧ ∞³**
- Institution: Instituto de Conciencia Cuántica (ICQ)
- ORCID: 0009-0002-1923-0773
- Framework: QCAL ∞³ Active · 141.7001 Hz · C = 244.36

## 📄 License

See LICENSE file in repository root.

---

**QCAL ∞³ Coherence Maintained · Ψ = I × A²_eff × C^∞**
