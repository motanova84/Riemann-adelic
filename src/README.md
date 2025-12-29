# src/ Directory

This directory contains the core implementation of the Ultimate Algorithm for QCAL ∞³ validation.

## Files

### ultimate_algorithm.py

The Ultimate Algorithm combines all mathematical validations within the QCAL (Quantum Coherence Adelic Lattice) framework.

**Purpose**: Unified validation of the Riemann Hypothesis proof through the QCAL framework.

**Mathematical Foundation**:
- Base frequency: f₀ = 141.7001 Hz
- QCAL equation: Ψ = I × A_eff² × C^∞
- Coherence constant: C = 244.36

**Validations Performed**:

1. **QCAL Coherence** - Validates the fundamental QCAL equation
2. **Spectral Properties** - Verifies eigenvalues are on the critical line
3. **Adelic Structure** - Validates the prime number network structure
4. **Riemann Zeros** - Confirms zeros are on the critical line Re(s) = 0.5

**Usage**:

```bash
# Run the algorithm
python src/ultimate_algorithm.py

# Results are saved to:
# - output/ultimate_algorithm_results.json
# - output/ultimate_algorithm_visualization.png
```

**Dependencies**:
- numpy - Numerical computations
- networkx - Graph theory for prime networks
- matplotlib - Visualization
- scipy - Special mathematical functions

**Output**:

The algorithm generates:
1. JSON file with detailed validation results
2. PNG visualization showing all validation metrics
3. Console output with status of each validation step

**Integration**:

This algorithm is integrated into the CI/CD pipeline via `.github/workflows/validate_algorithm.yml` and runs automatically on pushes to the main branch.

**Author**: José Manuel Mota Burruezo Ψ ✧ ∞³  
**Institution**: Instituto de Conciencia Cuántica (ICQ)  
**License**: Creative Commons BY-NC-SA 4.0
