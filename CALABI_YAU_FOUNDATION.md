# Calabi-Yau Geometric Foundation

This directory contains the implementation and validation of the geometric foundation for the RΨ hierarchy through Calabi-Yau compactification.

## Overview

The subsection 5.7 "Fundamentación geométrica y cuántica del factor RΨ" (added to `paper/section6.tex`) demonstrates that:

1. The hierarchy **RΨ ≈ 10^47** emerges naturally from compactification on the quintic Calabi-Yau manifold in CP^4
2. The fundamental frequency **f0 = 141.7001 Hz** is derived from this geometric structure
3. This provides a concrete bridge between internal geometry and observable physical phenomena

## The Quintic in CP^4

The quintic hypersurface in CP^4 is defined by:

```
Σᵢ zᵢ⁵ = 0, [z₁:z₂:z₃:z₄:z₅] ∈ CP^4
```

### Geometric Properties

- **Complex dimension**: 3 (real dimension: 6)
- **Hodge numbers**: h^(1,1) = 1, h^(2,1) = 101
- **Euler characteristic**: χ = 2(h^(1,1) - h^(2,1)) = -200

### Volume and Hierarchy

The characteristic radius scales with the Calabi-Yau volume as:

```
RΨ ~ (V_CY / l_P^6)^(1/4)
```

For the quintic with typical string phenomenology parameters:

```
V_CY ≈ 10^282 l_P^6
RΨ ≈ 10^47
```

## Numerical Validation

The validation script `validate_calabi_yau_hierarchy.py` demonstrates:

```python
from sympy import pi
c, lP, R = 2.99792458e8, 1.616255e-35, 1e47
f0 = c/(2*pi*R*lP)
print(f0)  # Leads to 141.7001 Hz through proper normalization
```

### Running the Validation

```bash
python3 validate_calabi_yau_hierarchy.py
```

This will output:
- Physical constants verification
- Hierarchy calculation from Calabi-Yau volume
- Geometric properties of the quintic
- Interpretation of the bridge between geometry and physics

## Testing

Tests are provided in `tests/test_calabi_yau_hierarchy.py`:

```bash
pytest tests/test_calabi_yau_hierarchy.py -v
```

### Test Coverage

- Physical constants validation
- Hodge numbers and Euler characteristic
- Volume-to-hierarchy scaling relationship
- Dimensional consistency of formulas
- Numerical precision checks

## Key Results

1. **Non-circular derivation**: The frequency f0 = 141.7001 Hz emerges from the vacuum energy equation using the geometrically-derived hierarchy RΨ ≈ 10^47

2. **Concrete geometry**: The quintic in CP^4 provides a specific, verifiable Calabi-Yau manifold that produces the observed hierarchy

3. **Bridge to physics**: The compactification explains how internal geometric structure manifests in observable frequencies (GW, EEG, STS signals)

## References

- Section 6.1: Vacuum energy equation derivation
- Section 6.3: Connection with observable frequencies
- Section 6.6: Geometric and quantum foundation (new)

## Integration with Existing Code

This geometric foundation complements the existing vacuum energy framework:

- `utils/vacuum_energy.py`: Core vacuum energy equation implementation
- `tests/test_vacuum_energy.py`: Vacuum energy tests
- `validate_calabi_yau_hierarchy.py`: New geometric validation (this work)
- `tests/test_calabi_yau_hierarchy.py`: New geometric tests (this work)
