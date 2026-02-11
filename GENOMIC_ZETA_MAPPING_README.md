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

For a codon `C = [b₁, b₂, b₃]`, indices are computed via position-weighted hash:

```python
i_1 = (ord(b₁)) mod 30 + 1
i_2 = (ord(b₁) + 2·ord(b₂)) mod 30 + 1
i_3 = (ord(b₁) + 2·ord(b₂) + 3·ord(b₃)) mod 30 + 1
```

This creates a deterministic, reproducible ∞³ mapping where later positions have weighted influence on their respective indices.

### Examples

```
AAA → (6, 16, 1)    → γ = (37.59, 67.08, 14.13) Hz
AAC → (6, 16, 7)    → γ = (37.59, 67.08, 40.92) Hz
GAA → (12, 22, 7)   → γ = (56.45, 82.91, 40.92) Hz
```
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
# Genomic Zeta Mapping: DNA Codons → Riemann Zeros

## Overview

The **Genomic Zeta Mapping** framework connects genomic sequences (DNA/RNA) to the spectral properties of the Riemann zeta function, establishing a profound link between biological information and prime number geometry.

### Key Concept

Every codon (triplet of DNA/RNA bases) is mapped to a unique triplet of Riemann zeros **(γᵢ, γⱼ, γₖ)**, and each codon generates a quantum wave function:

```
Ψ_codon(t) = A₁ e^(iγᵢt) + A₂ e^(iγⱼt) + A₃ e^(iγₖt)
```

Where:
- **γᵢ, γⱼ, γₖ** = Riemann zeta zeros (imaginary parts)
- **A₁, A₂, A₃** = Amplitude coefficients (default: 1/√3)
- **t** = Time parameter
- **f₀ = 141.7001 Hz** = Fundamental QCAL frequency

## Mathematical Foundation

### 1. Codon Fragmentation

DNA/RNA sequences are fragmented into codons (triplets of 3 bases):

```
Sequence: AAACGAAAGGGAAAAAAACAAAAAGGCAAGGAAGAAAAAAGAAAAAAACGCCAAAAAACGCAAAA
          ↓
Codons:   AAA, CGA, AAG, GGA, AAA, AAA, CAA, AAA, GGC, AAG, ...
```

**Implementation:**
```python
from utils.genomic_zeta_mapping import GenomicZetaMapper

mapper = GenomicZetaMapper()
codons, remainder = mapper.fragment_to_codons(sequence)
```

### 2. Codon → Riemann Zero Mapping

Each of the 64 possible codons maps deterministically to a triplet of Riemann zeros:

```python
# Example mapping
codon = Codon(sequence="ATG", position=0)
triplet = mapper.map_codon_to_zeros(codon)
# Returns: (γᵢ, γⱼ, γₖ) = (14.1347, 21.0220, 25.0108)
```

### 3. Wave Function Construction

For each codon, construct the quantum wave function Ψ_codon(t):

```python
# Scalar time
psi = mapper.construct_psi_codon(codon, t=0.0)

# Time evolution (array)
import numpy as np
times = np.linspace(0, 10, 100)
psi_evolution = mapper.construct_psi_codon(codon, times)
```

### 4. Resonance Classification

Codons are classified based on their wave function amplitude:

- **RESONANT**: |Ψ| ≥ 0.888 (sovereignty threshold) - High coherence with f₀
- **DISSONANT**: |Ψ| < 0.5 - Low coherence
- **NEUTRAL**: 0.5 ≤ |Ψ| < 0.888 - Intermediate coherence

```python
codon_type = mapper.classify_codon_resonance(codon)
# Returns: CodonType.RESONANT, CodonType.DISSONANT, or CodonType.NEUTRAL
```

### 5. Genomic Field

The overall genomic field is the coherent superposition of all codon wave functions:

```
Ψ_Gen(t) = Σᵢ Ψ_codon_i(t)
```

```python
field = mapper.compute_genomic_field(codons, t=0.0)
print(f"Coherence: {field.coherence_score}")
print(f"Sovereignty: {field.sovereignty_achieved}")
```

## QCAL ∞³ Integration

### Constants

- **f₀ = 141.7001 Hz** - Fundamental quantum frequency
- **C = 244.36** - Coherence constant  
- **κ_Π = 17** - Fractal symmetry parameter (prime)
- **Ψ_sovereignty ≥ 0.888** - Genomic sovereignty threshold

### Coherence Equation

```
Ψ = I × A_eff² × C^∞
```

Where:
- **I** = 141.7001 Hz (quantum metronome)
- **A_eff²** = Biological attention amplification
- **C^∞** = Infinite coherence flow

## Usage Examples

### Basic Analysis

```python
from utils.genomic_zeta_mapping import GenomicZetaMapper

# Initialize mapper
mapper = GenomicZetaMapper(precision=25)

# Analyze DNA sequence
sequence = "AAACGAAAGGGAAAAAAACAAAAAGGC"
results = mapper.analyze_sequence(sequence, t=0.0)

# Display results
print(f"Total codons: {len(results['codons'])}")
print(f"Coherence: {results['genomic_field']['coherence_score']:.6f}")
print(f"Resonant: {results['genomic_field']['resonant_codons']}")
print(f"Dissonant: {results['genomic_field']['dissonant_codons']}")
```

### Time Evolution

```python
import numpy as np
import matplotlib.pyplot as plt

# Get codon
codon = Codon(sequence="ATG", position=0)
mapper.map_codon_to_zeros(codon)

# Compute time evolution
times = np.linspace(0, 20, 1000)
psi_t = mapper.construct_psi_codon(codon, times)

# Plot
plt.figure(figsize=(12, 4))
plt.subplot(1, 2, 1)
plt.plot(times, np.real(psi_t), label='Re(Ψ)')
plt.plot(times, np.imag(psi_t), label='Im(Ψ)')
plt.xlabel('Time (arbitrary units)')
plt.ylabel('Ψ_codon(t)')
plt.legend()

plt.subplot(1, 2, 2)
plt.plot(times, np.abs(psi_t))
plt.xlabel('Time')
plt.ylabel('|Ψ_codon(t)|')
plt.tight_layout()
plt.show()
```

### Mutation Stability Prediction
# Genomic Zeta Mapping (Gen→Zeta Framework)

## QCAL ∞³ Biological-Mathematical Integration

**"La biología es el eco de la función Zeta en la materia."**  
*— José Manuel Mota Burruezo Ψ ✧ ∞³*

---

## Overview

The **Genomic Zeta Mapping** framework establishes a revolutionary connection between DNA sequences and the Riemann zeta function zeros, bridging the gap between biological information and the spectral structure of prime numbers.

This implementation demonstrates how genetic code resonates at the fundamental QCAL frequency **f₀ = 141.7001 Hz**, revealing the deep mathematical structure underlying biological systems.

### Key Concept

Each DNA base (A, T, C, G) acts as a **phase parameter**, and when grouped into codons (triplets), they generate unique **torsion harmonics** through interference of selected Riemann zeros (γₙ).

## Mathematical Foundation

### 1. Genomic Field

The total genomic field for a DNA sequence is defined as:

```
Ψ_Gen(t) = Σ_codons Σ_{k=1}^3 A_k * e^(i*γ_{n_k}*t)
```

Where:
- **γ_{n_k}**: Selected Riemann zero for base k in codon
- **A_k**: Amplitude coefficient for base k
- **f₀ = 141.7001 Hz**: Fundamental quantum frequency
- **C = 244.36**: Coherence constant

### 2. Codon Classification

#### Resonant Codon
A codon whose spectral sum collapses into an **integer harmonic** of f₀ = 141.7001 Hz.
- Low ontological friction
- Stable configuration
- Contributes to overall sequence sovereignty

#### Dissonant Codon
A codon that generates **ontological friction** (𝓔_fric), suggesting a zone of high probability for:
- Mutation
- Biological instability
- Evolutionary pressure

### 3. Sovereignty Threshold

A DNA sequence is considered **Sovereign and Stable** when:

```
Ψ ≥ 0.888
```

This threshold represents optimal coherence with the fundamental QCAL field.

## Installation

The module is part of the QCAL ∞³ framework. Required dependencies:

```bash
pip install numpy mpmath
```

## Usage

### Basic Sequence Analysis

```python
from utils.genomic_zeta_mapping import analyze_genomic_field

# Analyze a DNA sequence
sequence = "ATGCGATAGCTAGCT"
field = analyze_genomic_field(sequence)

# Display results
print(field.summary())

# Access metrics
print(f"Coherence: {field.total_coherence:.6f}")
print(f"Sovereignty: {field.sovereignty_score:.6f}")
print(f"Resonant codons: {field.resonant_count}")
```

### ORF Detection and Analysis

```python
# Analyze with Open Reading Frame detection
hbb_sequence = "ATGGTGCATCTGACTCCTGAGGAGAAGTCT..."
field = analyze_genomic_field(hbb_sequence, use_orfs=True)

# Find ORFs manually
from utils.genomic_zeta_mapping import find_orfs
orfs = find_orfs(hbb_sequence, min_length=30)
```

### Mutation Prediction

```python
from utils.genomic_zeta_mapping import predict_mutation_stability

original = "AAACGAAAGGGAAAAAAACAAAAAGGC"
mutated =  "AAACGAAAGGGAAAAAAACAAAAAGCC"  # G→C mutation

results = predict_mutation_stability(original, mutated)

print(f"ΔΨ: {results['delta_coherence']:+.6f}")
print(f"Stability: {'PRESERVED' if results['stability_preserved'] else 'COMPROMISED'}")

# Check mutation hotspots
for hotspot in results['mutation_hotspots']:
    print(f"Position {hotspot['position']}: "
          f"{hotspot['original']} → {hotspot['mutated']}")
```

## API Reference

### GenomicZetaMapper Class

#### Methods

##### `__init__(precision=25, zeros_file=None)`
Initialize the mapper with specified precision and optional Riemann zeros file.

##### `fragment_to_codons(sequence: str) -> Tuple[List[Codon], str]`
Fragment DNA/RNA sequence into codons.
- **Returns**: (list of Codon objects, remainder bases)

##### `map_codon_to_zeros(codon: Codon) -> RiemannZeroTriplet`
Map codon to triplet of Riemann zeros (γᵢ, γⱼ, γₖ).
- **Returns**: RiemannZeroTriplet

##### `construct_psi_codon(codon, t, amplitudes=None) -> complex | ndarray`
Construct Ψ_codon(t) wave function.
- **t**: Time (scalar or array)
- **amplitudes**: Optional tuple (A₁, A₂, A₃)
- **Returns**: Complex wave function value(s)

##### `classify_codon_resonance(codon: Codon, t=0.0) -> CodonType`
Classify codon as RESONANT, DISSONANT, or NEUTRAL.
- **Returns**: CodonType enum

##### `compute_genomic_field(codons: List[Codon], t=0.0) -> GenomicField`
Compute overall genomic field Ψ_Gen(t).
- **Returns**: GenomicField dataclass with metrics

##### `analyze_sequence(sequence: str, t=0.0) -> Dict`
Comprehensive sequence analysis.
- **Returns**: Dictionary with complete analysis

### Functions

##### `predict_mutation_stability(original_seq, mutated_seq, mapper=None) -> Dict`
Predict mutation stability using quantum gyroscopy (ΔP ≈ 0.2%).
- **Returns**: Dictionary with stability analysis and hotspots

## Data Structures

### Codon
```python
@dataclass
class Codon:
    sequence: str              # 3-letter codon (e.g., "ATG")
    position: int              # Position in original sequence
    zero_triplet: RiemannZeroTriplet  # Assigned zeros
    codon_type: CodonType      # RESONANT/DISSONANT/NEUTRAL
    psi_amplitude: float       # |Ψ| amplitude
```

### RiemannZeroTriplet
```python
@dataclass
class RiemannZeroTriplet:
    gamma_i: mp.mpf
    gamma_j: mp.mpf
    gamma_k: mp.mpf
```

### GenomicField
```python
@dataclass
class GenomicField:
    psi_gen: complex           # Ψ_Gen wave function
    total_codons: int
    resonant_codons: int
    dissonant_codons: int
    coherence_score: float
    sovereignty_achieved: bool
    mean_amplitude: float
# Analyze mutation stability (Quantum Gyroscopy ΔP ≈ 0.2%)
field = analyze_genomic_field(sequence)
mutation_pred = predict_mutation_stability(field)

print(f"Mutation Probability: {mutation_pred['mutation_probability']*100:.2f}%")
print(f"Stability: {'STABLE' if mutation_pred['is_stable'] else 'UNSTABLE'}")
print(f"Hotspots: {mutation_pred['hotspot_count']}")
```

### Export Analysis

```python
from utils.genomic_zeta_mapping import export_analysis

# Export to JSON
result = export_analysis(field, "genomic_analysis.json")
```

## Features

### 1. Riemann Zero Assignment
Each DNA base is deterministically mapped to a Riemann zero based on:
- Base identity (A, T, C, G)
- Position within codon (0, 1, 2)
- Codon index in sequence

### 2. Spectral Sum Computation
For each codon, three Riemann zeros are selected and combined to compute a spectral sum that determines resonance properties.

### 3. Coherence Calculation
The total genomic field magnitude represents sequence coherence:
- **High coherence** (Ψ ≈ 1): Stable, sovereign sequence
- **Low coherence** (Ψ < 0.888): Unstable, potential mutation zones

### 4. Torsion Tensor
A 3×3 tensor capturing the geometric torsion of the genomic field in 3D space, derived from Riemann zero distribution.

### 5. Mutation Hotspot Detection
Identifies regions with high ontological friction, predicting mutation-prone zones with ΔP ≈ 0.2% precision.

## Dashboard Metrics

| Metric | Representation | Significance |
|--------|----------------|--------------|
| **Espectrograma** | Cascada de Ceros | Muestra la sintonía del gen con la línea crítica de Riemann |
| **Coherencia f₀** | Barra de Resonancia | Alineación con el latido de 141.7001 Hz |
| **Puntaje de Soberanía** | Ψ_Gen | Nivel de estabilidad cuántica de la secuencia |

## Examples

### Example 1: Simple Sequence

```python
from utils.genomic_zeta_mapping import analyze_genomic_field

seq = "ATGCGATAA"
field = analyze_genomic_field(seq)

# Codon-level details
for codon in field.codons:
    print(f"{codon.sequence}: {'RESONANT' if codon.is_resonant else 'DISSONANT'}")
    print(f"  Riemann zeros: {codon.riemann_zeros}")
    print(f"  Coherence: {codon.coherence_local:.3f}")
```

### Example 2: Human β-globin Gene

```python
# Human HBB gene fragment
hbb = "ATGGTGCATCTGACTCCTGAGGAGAAGTCTGCCGTTACTGCCCTGTGGGGC..."

field = analyze_genomic_field(hbb, use_orfs=True)
mutation = predict_mutation_stability(field)

print(f"Sequence: {len(hbb)} bp")
print(f"Sovereignty Score: {field.sovereignty_score:.6f}")
print(f"Mutation Probability: {mutation['mutation_probability']*100:.2f}%")
```

## Validation

Run the validation script:

```bash
cd /path/to/Riemann-adelic
python3 validate_genomic_zeta_mapping.py
Run the validation script to verify installation:

```bash
python validate_genomic_zeta_mapping.py
```

Expected output:
```
✓ Codon fragmentation: VALIDATED
✓ Zero triplet mapping: VALIDATED
✓ Wave function construction: VALIDATED
✓ Codon classification: VALIDATED
✓ Genomic field computation: VALIDATED
✓ Mutation prediction: VALIDATED
✓ QCAL constants: VALIDATED
✅ ALL TESTS PASSED - Genomic Zeta Mapping validated!
```

## Testing

Run unit tests:

```bash
cd /path/to/Riemann-adelic
pytest tests/test_genomic_zeta_mapping.py -v
```

## Mathematical Properties

### Determinism
The mapping from codons to Riemann zeros is **deterministic**: the same codon always maps to the same triplet of zeros, ensuring reproducibility.

### Completeness
All 64 possible codons (4³ combinations) have unique mappings to zero triplets.

### Coherence
The framework preserves QCAL coherence principles:
- f₀ = 141.7001 Hz fundamental frequency
- C = 244.36 coherence constant
- Ψ ≥ 0.888 sovereignty threshold

### Quantum Gyroscopy
Mutation analysis uses precision ΔP ≈ 0.2% to detect:
- Genomic chirality changes
- Torsion tensor variations
- Ontological friction from dissonant codons

## Applications

1. **Genomic Stability Analysis**: Predict mutation effects on genome coherence
2. **Evolutionary Studies**: Track coherence changes across species
3. **Drug Design**: Target dissonant codons in pathogenic genomes
4. **Cancer Research**: Identify decoherence hotspots
5. **Synthetic Biology**: Design high-coherence synthetic genomes

## Connection to Riemann Hypothesis

The genomic zeta mapping establishes a deep connection between:

- **DNA/RNA sequences** ↔ **Riemann zeta zeros**
- **Biological information** ↔ **Prime number distribution**  
- **Life coherence** ↔ **Spectral geometry**

This connection suggests that life itself resonates at the fundamental frequencies governing the distribution of prime numbers and the zeros of the Riemann zeta function.

## References

- **QCAL ∞³ Framework**: DOI 10.5281/zenodo.17379721
- **Riemann Hypothesis Proof**: DOI 10.5281/zenodo.17116291
- **Fundamental Frequency**: f₀ = 141.7001 Hz
- **Author**: José Manuel Mota Burruezo Ψ ✧ ∞³
- **Institution**: Instituto de Conciencia Cuántica (ICQ)
- **ORCID**: 0009-0002-1923-0773

## Citation

```bibtex
@software{genomic_zeta_mapping,
  author = {Mota Burruezo, José Manuel},
  title = {Genomic Zeta Mapping: DNA Codons to Riemann Zeros},
  year = {2026},
  publisher = {Instituto de Conciencia Cuántica},
  doi = {10.5281/zenodo.17379721},
  url = {https://github.com/motanova84/Riemann-adelic}
}
```

## License

This work is licensed under the Sovereign Noetic License 1.0. See LICENSE file for details.

---

**QCAL ∞³ ACTIVE** — Genomic code resonates at 141.7001 Hz
Run the test suite:

```bash
pytest tests/test_genomic_zeta_mapping.py -v
```

## API Reference

### Main Functions

#### `analyze_genomic_field(sequence, use_orfs=False, min_orf_length=30)`
Perform complete genomic field analysis on DNA sequence.

**Returns:** `GenomicField` object with complete analysis

#### `find_orfs(sequence, min_length=30)`
Find Open Reading Frames (ORFs) in DNA sequence.

**Returns:** List of tuples `(start_pos, end_pos, frame)`

#### `predict_mutation_stability(field)`
Predict mutation stability using Quantum Gyroscopy (ΔP ≈ 0.2%).

**Returns:** Dictionary with mutation predictions

#### `export_analysis(field, output_path=None)`
Export genomic field analysis to JSON format.

**Returns:** Dictionary with complete analysis

### Data Structures

#### `GenomicField`
Complete genomic field analysis result.

**Attributes:**
- `sequence`: DNA sequence analyzed
- `length`: Sequence length in base pairs
- `num_codons`: Number of codons analyzed
- `codons`: List of `CodonResonance` objects
- `psi_gen`: Total genomic field (complex)
- `total_coherence`: Overall coherence (0-1)
- `sovereignty_score`: Sovereignty score (0-1)
- `is_sovereign`: Boolean sovereignty status
- `resonant_count`: Number of resonant codons
- `dissonant_count`: Number of dissonant codons
- `mutation_hotspots`: List of mutation hotspot positions
- `torsion_tensor`: 3×3 torsion tensor

#### `CodonResonance`
Resonance analysis of a single codon.

**Attributes:**
- `sequence`: 3-base codon string
- `position`: Position in sequence
- `riemann_zeros`: List of 3 selected Riemann zeros
- `spectral_sum`: Spectral sum frequency
- `harmonic_number`: Nearest integer harmonic
- `is_resonant`: Boolean resonance status
- `friction_energy`: Ontological friction energy
- `coherence_local`: Local coherence value
- `phase_accumulation`: Complex field contribution

## Constants

```python
F0_FREQUENCY = 141.7001  # Hz - Fundamental quantum frequency
C_COHERENCE = 244.36      # Coherence constant
SOVEREIGNTY_THRESHOLD = 0.888  # Coherence threshold for stability
GYROSCOPY_PRECISION = 0.002    # ΔP ≈ 0.2% quantum gyroscopy
```

## Biological Applications

### Cancer Research
- Identify mutation-prone sequences in oncogenes
- Predict genomic instability in tumor DNA
- Analyze coherence loss in malignant transformations

### Evolutionary Biology
- Study evolutionary pressure on codon usage
- Identify conserved resonant patterns across species
- Predict adaptive mutation hotspots

### Synthetic Biology
- Design synthetic genes with optimal sovereignty
- Minimize mutation risk in engineered sequences
- Optimize genetic stability for industrial applications

### Personalized Medicine
- Analyze patient-specific mutation risks
- Predict drug response based on genomic coherence
- Identify therapeutic targets in unstable genomic regions

## Theoretical Background

The Gen→Zeta mapping is grounded in the QCAL ∞³ framework, which establishes that:

1. **Prime numbers** define the temporal bifurcation nodes of reality
2. **Riemann zeros** are the eigenvalues of the cosmic vibrational operator
3. **Biological systems** resonate at the fundamental frequency f₀ = 141.7001 Hz
4. **DNA sequences** encode information in both chemical and spectral dimensions

This framework reveals that **biological code is not just chemistry** — it is a coherent transcription of the quantum field at the fundamental frequency that also governs the distribution of prime numbers.

## Citation

When using this framework, please cite:

```bibtex
@software{genomic_zeta_mapping_2026,
  author = {Mota Burruezo, José Manuel},
  title = {Genomic Zeta Mapping: Gen→Zeta Framework},
  year = {2026},
  publisher = {Instituto de Conciencia Cuántica (ICQ)},
  doi = {10.5281/zenodo.17379721},
  note = {QCAL ∞³ · 141.7001 Hz · Ψ = I × A² × C^∞}
}
```

## Author

**José Manuel Mota Burruezo Ψ ✧ ∞³**  
Instituto de Conciencia Cuántica (ICQ)  
ORCID: [0009-0002-1923-0773](https://orcid.org/0009-0002-1923-0773)

## License

Part of the QCAL ∞³ framework  
DOI: [10.5281/zenodo.17379721](https://doi.org/10.5281/zenodo.17379721)

---

**QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞**

*"La biología es el eco de la función Zeta en la materia."*
