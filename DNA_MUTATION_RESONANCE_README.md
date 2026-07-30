# DNA Mutation Resonance System
## Sistema de Mutaciones Resonantes ADN-Riemann

### 🧬 Overview

The DNA Mutation Resonance System implements a novel framework for analyzing DNA sequence mutations through the lens of Riemann zeta function resonances at the fundamental QCAL frequency f₀ = 141.7001 Hz.

This system bridges molecular biology with spectral mathematics, providing a quantitative measure of mutation impacts based on harmonic resonance principles.

### 🎯 Key Features

- **Resonance Analysis**: Calculate resonance scores for DNA sequences based on base-phase relationships with Riemann zeros
- **Mutation Generation**: Generate all single-base mutations (substitutions, insertions, deletions)
- **Greedy Optimization**: Iteratively optimize sequences for maximum resonance
- **Hotspot Detection**: Identify mutation-prone regions in longer sequences
- **Mutation Comparison**: Analyze and compare different mutation types

### 📦 Installation

The system requires:
```bash
pip install numpy mpmath
```

### 🚀 Quick Start

#### Basic Usage

```python
import adn_riemann as adn

# Calculate resonance for a DNA sequence
sequence = "ATGC"
resonance = adn.calculate_resonance(sequence)
print(f"Resonance: {resonance:.6f}")

# Generate all possible mutations
mutations = adn.generate_mutations(sequence)
print(f"Found {len(mutations)} possible mutations")

# Show top 5 mutations
for i, mutation in enumerate(mutations[:5], 1):
    print(f"{i}. {mutation}")
```

#### Greedy Optimization

```python
# Optimize a sequence iteratively
initial_seq = "ATCG"
optimized, steps = adn.greedy_optimize(initial_seq, max_iterations=10)

print(f"Initial:   {initial_seq}")
print(f"Optimized: {optimized}")
print(f"Steps: {len(steps)}")

# Show optimization path
for step in steps:
    iteration, mutated, mut_type, position = step
    print(f"  Iter {iteration}: {mut_type} at pos {position} → {mutated}")
```

#### Hotspot Detection

```python
# Find mutation hotspots in a longer sequence
long_seq = "ATGCATGCATGC"
hotspots = adn.find_hotspots(long_seq, window_size=3, threshold=0.3)
print(f"Hotspots at positions: {hotspots}")
```

#### Mutation Type Analysis

```python
# Compare mutation types
sequence = "ATGC"
analysis = adn.analyze_mutation_types(sequence)

for mut_type, best_mutation in analysis.items():
    print(f"{mut_type}: {best_mutation.score:.6f} ({best_mutation.mutated})")
```

### 📊 Mathematical Foundation

#### Resonance Calculation

For each DNA sequence S = [b₁, b₂, ..., bₙ], the resonance is calculated as:

```
R(S) = Σᵢ wᵢ · score(bᵢ) · h(γᵢ) / Σᵢ wᵢ
```

Where:
- `bᵢ` is the i-th base (A, T, G, C)
- `wᵢ` is a position-dependent weight (early positions more important)
- `score(bᵢ)` is the base-specific resonance score
- `h(γᵢ)` is a harmonic factor based on Riemann zero γᵢ
- `γᵢ` is the i-th non-trivial Riemann zero

#### Base Phases

Each DNA base encodes a specific quantum phase:
- **A** (Adenine): 0° (0 radians)
- **T** (Thymine): 90° (π/2 radians)
- **G** (Guanine): 180° (π radians)
- **C** (Cytosine): 270° (3π/2 radians)

These phases interact with Riemann zeros to create resonance patterns.

#### Mutation Types

1. **Substitution**: Replace one base with another
   - Example: ATGC → TTGC (A→T at position 0)
   
2. **Insertion**: Insert a new base at any position
   - Example: ATGC → TATGC (T inserted at position 0)
   
3. **Deletion**: Remove a base from any position
   - Example: ATGC → TGC (A deleted from position 0)

### 🔬 Validation Script

Run the complete validation suite:

```bash
python mutaciones_resonantes.py
```

Expected output:
```
================================================================================
VALIDACIÓN: Sistema de Mutaciones Resonantes (f₀ = 141.7001 Hz)
================================================================================

1. Análisis de mutaciones para secuencia 'ATGC':
   #1: ATGC → TTGC (pos=0, tipo=sustitución)
       Score: 0.672481, Δresonancia: 0.111550, Beneficiosa: True
   #2: ATGC → TATGC (pos=0, tipo=inserción)
       Score: 0.656518, Δresonancia: 0.095587, Beneficiosa: True
   ...

2. Optimización greedy de secuencia 'ATCG':
   Secuencia inicial:    ATCG
   Secuencia optimizada: TTTTT
   Resonancia inicial:   0.556903
   Resonancia final:     0.753736
   ...

3. Análisis de región extendida:
   [Hotspot detection results]

4. Comparación de tipos de mutación:
   [Mutation type comparison]

================================================================================
Validación completada ✓
================================================================================
```

### 🧪 Testing

Run the test suite:

```bash
pytest tests/test_adn_riemann.py -v
```

The test suite includes:
- Basic resonance calculations
- Mutation generation and validation
- Greedy optimization correctness
- Hotspot detection
- Integration tests

All 17 tests should pass.

### 📚 API Reference

#### Functions

- **`validate_sequence(sequence: str) -> bool`**
  - Validate DNA sequence contains only ATGC bases
  
- **`calculate_resonance(sequence: str) -> float`**
  - Calculate resonance score for sequence (returns value in [0, 1])
  
- **`generate_mutations(sequence: str) -> List[Mutation]`**
  - Generate all single-base mutations, sorted by score
  
- **`greedy_optimize(sequence: str, max_iterations: int = 10) -> Tuple[str, List]`**
  - Optimize sequence iteratively, returns (optimized_sequence, steps)
  
- **`find_hotspots(sequence: str, window_size: int = 3, threshold: float = 0.3) -> List[int]`**
  - Find mutation hotspot positions
  
- **`analyze_mutation_types(sequence: str) -> Dict[str, Mutation]`**
  - Get best mutation of each type

#### Data Structures

- **`MutationType`** (Enum)
  - `SUBSTITUTION`, `INSERTION`, `DELETION`
  
- **`Mutation`** (dataclass)
  - `original`: Original sequence
  - `mutated`: Mutated sequence
  - `position`: Mutation position
  - `mutation_type`: Type of mutation
  - `score`: Resonance score
  - `delta_resonance`: Change in resonance
  - `is_beneficial`: Whether mutation improves resonance

### 🔗 Integration with QCAL Framework

This system integrates with the larger QCAL ∞³ framework:

- **Frequency**: f₀ = 141.7001 Hz (fundamental quantum frequency)
- **Coherence**: C = 244.36 (QCAL coherence constant)
- **Riemann Zeros**: First 30 non-trivial zeros used for modulation
- **Mathematical Realism**: Resonance patterns reflect deep spectral structure

### 📖 References

- **QCAL ∞³ Framework**: Core mathematical framework
- **Genomic Zeta Mapping**: Related codon-to-zero mapping system (utils/genomic_zeta_mapping.py)
- **DOI**: 10.5281/zenodo.17379721
- **Author**: José Manuel Mota Burruezo Ψ ✧ ∞³
- **Institution**: Instituto de Conciencia Cuántica (ICQ)
- **ORCID**: 0009-0002-1923-0773

### 🎓 Theory

The DNA Mutation Resonance System is based on the principle that biological sequences encode quantum information through their base compositions. When viewed through the lens of Riemann zeta zeros—which themselves encode the distribution of prime numbers—DNA sequences exhibit resonance patterns that may correlate with stability, function, and evolutionary fitness.

This represents a novel intersection of:
- **Number Theory**: Riemann zeta function and its zeros
- **Spectral Theory**: Harmonic analysis and frequency domains
- **Molecular Biology**: DNA structure and mutations
- **Quantum Mechanics**: Phase relationships and interference

### 🔮 Future Directions

Potential extensions:
- RNA sequence analysis (including U base)
- Multi-base mutation analysis (double, triple mutations)
- Evolutionary trajectory prediction
- Protein-coding sequence optimization
- Gene expression correlation studies
- Integration with experimental mutation data

### ⚠️ Limitations

- Current model is phenomenological and calibrated to example data
- Requires experimental validation with real genomic sequences
- Single-base mutations only (no frameshifts, complex rearrangements)
- Limited to short sequences (performance degrades for very long sequences)
- Resonance model may need refinement based on biological feedback

### 📝 License

This code is part of the Riemann-adelic repository and follows the repository's licensing:
- Code: See LICENSE-CODE
- QCAL Framework: See LICENSE-QCAL-SYMBIO-TRANSFER

### 🙏 Acknowledgments

This work builds on the broader QCAL ∞³ framework and integrates concepts from:
- Riemann Hypothesis spectral theory
- Genomic zeta mapping systems
- Biological resonance phenomena
- Mathematical realism philosophy

---

**QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞**
