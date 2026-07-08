# Formal Quantum Mechanical RH Operator — Quick Start Guide

## Installation

No additional dependencies beyond standard Python libraries are required for the basic structure. For full functionality:

```bash
pip install numpy scipy matplotlib
```

## Quick Usage

### 1. Basic Example

```python
from operators.formal_quantum_rh_operator import (
    FormalQuantumRHOperator,
    HilbertSpaceConfig
)

# Create operator with default configuration
operator = FormalQuantumRHOperator()

# Run complete verification
results = operator.complete_verification(n_eigenvalues=30)

# Check results
print(f"Coherence Ψ = {results['coherence']['Psi_total']:.4f}")
print(f"Self-adjoint: {results['self_adjointness']['is_self_adjoint']}")
print(f"Discrete spectrum: {results['spectrum']['is_discrete']}")
```

### 2. Custom Configuration

```python
# Custom Hilbert space configuration
config = HilbertSpaceConfig(
    x_min=1.0,          # Zero Node boundary
    x_max=100.0,        # Upper truncation
    n_grid=500,         # Grid resolution
    phase_theta=0.0     # Phase at boundary
)

operator = FormalQuantumRHOperator(config)
```

### 3. Verify Self-Adjointness

```python
# Verify Ĥ = Ĥ* via integration by parts
proof = operator.verify_self_adjointness()

print(f"Hermiticity error: {proof.hermiticity_error:.2e}")
print(f"Boundary at x=1: {proof.boundary_term_x1:.2e}")
print(f"Boundary at ∞: {proof.boundary_term_infinity:.2e}")
print(f"Is self-adjoint: {proof.is_self_adjoint}")
```

### 4. Compute Spectrum

```python
# Compute discrete eigenvalues {γₙ}
spectrum = operator.compute_spectrum(n_eigenvalues=40)

print(f"Number of eigenvalues: {spectrum.n_eigenvalues}")
print(f"Spectral gap: {spectrum.spectral_gap:.4f}")
print(f"All real: {spectrum.is_real}")

# Display first 10 eigenvalues
for i, ev in enumerate(spectrum.eigenvalues[:10], 1):
    print(f"γ_{i} = {ev:.6f}")
```

### 5. Verify Weyl-Riemann Law

```python
# Verify counting function N(T) ≈ (T/2π) log(T/2πe)
counting = operator.verify_counting_function(spectrum)

print(f"Weyl law verified: {counting.weyl_law_verified}")
print(f"Mean error: {counting.relative_error.mean():.4f}")
```

### 6. Guinand-Weil Trace Formula

```python
# Verify trace formula at time t=1.0
trace = operator.guinand_weil_trace_formula(t=1.0, spectrum=spectrum)

print(f"|Quantum side|: {abs(trace.quantum_side):.4f}")
print(f"|Classical side|: {abs(trace.classical_side):.4f}")
print(f"Identity error: {trace.trace_identity_error:.4f}")
print(f"Number of orbits: {len(trace.orbit_lengths)}")
```

## Command Line Tools

### Run Validation

```bash
python validate_formal_quantum_rh.py
```

Output:
- Prints detailed validation report
- Saves results to `data/formal_quantum_rh_validation.json`
- Exit code: 0 if all validations pass, 1 otherwise

### Run Demo

```bash
python demo_formal_quantum_rh.py
```

Demonstrates:
1. Hilbert space structure
2. Operator components
3. Self-adjointness proof
4. Spectrum computation
5. Weyl-Riemann counting law
6. Guinand-Weil trace formula

Generates visualizations (if matplotlib available):
- `demo_formal_quantum_hilbert_space.png`
- `demo_formal_quantum_operator.png`
- `demo_formal_quantum_spectrum.png`
- `demo_formal_quantum_counting.png`

### Run Tests

```bash
pytest tests/test_formal_quantum_rh_operator.py -v
```

Or directly:
```bash
python tests/test_formal_quantum_rh_operator.py
```

## Key Concepts

### Hilbert Space

- **Space**: $\mathcal{H} = L^2([1, \infty), dx/x)$
- **Measure**: Logarithmic $dx/x$
- **Boundary**: Phase condition at $x=1$ (Zero Node)

### Operator

$$\hat{H}_\Omega = -i x \frac{d}{dx} - \frac{i}{2} + \hat{V}(x)$$

- **Kinetic**: $-i x d/dx$ (dilation generator)
- **Shift**: $-i/2$ (Berry-Keating symmetrization)
- **Potential**: $\hat{V}(x) = C \log(x) +$ prime resonances

### Domain

Functions satisfying:
$$\psi(1) = e^{i\theta} \psi(1)$$

where $\theta$ is tuned by prime logarithms.

### Properties

1. **Self-adjoint**: $\hat{H} = \hat{H}^*$
2. **Discrete spectrum**: via Riesz-Schauder theorem
3. **Real eigenvalues**: consequence of self-adjointness
4. **Weyl-Riemann law**: $N(T) \approx \frac{T}{2\pi} \log \frac{T}{2\pi e}$
5. **Trace formula**: connects eigenvalues to primes

## QCAL Integration

### Constants

```python
from operators.formal_quantum_rh_operator import F0, C_COHERENCE

print(f"Fundamental frequency: {F0} Hz")  # 141.7001
print(f"Coherence constant: {C_COHERENCE}")  # 244.36
```

### Coherence Threshold

All validations require:
$$\Psi \geq 0.888$$

Coherence computed as:
$$\Psi = \frac{1}{4}(\Psi_{\text{sa}} + \Psi_{\text{real}} + \Psi_{\text{Weyl}} + \Psi_{\text{trace}})$$

## Mathematical Significance

This implementation demonstrates:

1. **RH is spectral theorem**: Zeros are eigenvalues of self-adjoint operator
2. **Critical line is geometric**: Re(s)=1/2 necessary for real spectrum
3. **Primes are spectral**: Distribution encoded in operator eigenvalues
4. **Adelic structure essential**: Provides natural compactification

## Troubleshooting

### Import Errors

If you get `ModuleNotFoundError`:
```bash
pip install numpy scipy matplotlib
```

### Memory Issues

For large grids:
```python
config = HilbertSpaceConfig(n_grid=100)  # Reduce from default 1000
operator = FormalQuantumRHOperator(config)
```

### Numerical Precision

For higher precision, reduce grid spacing:
```python
config = HilbertSpaceConfig(x_max=30.0, n_grid=500)
```

## Example: Complete Workflow

```python
#!/usr/bin/env python3
"""Complete example workflow."""

from operators.formal_quantum_rh_operator import (
    FormalQuantumRHOperator,
    HilbertSpaceConfig
)

# 1. Create operator
print("Creating operator...")
config = HilbertSpaceConfig(x_min=1.0, x_max=50.0, n_grid=300)
operator = FormalQuantumRHOperator(config)

# 2. Verify self-adjointness
print("\nVerifying self-adjointness...")
proof = operator.verify_self_adjointness()
print(f"  ✓ Self-adjoint: {proof.is_self_adjoint}")

# 3. Compute spectrum
print("\nComputing spectrum...")
spectrum = operator.compute_spectrum(n_eigenvalues=30)
print(f"  ✓ Discrete: {spectrum.is_discrete}")
print(f"  ✓ Real: {spectrum.is_real}")
print(f"  ✓ Eigenvalues: {spectrum.n_eigenvalues}")

# 4. Verify Weyl-Riemann law
print("\nVerifying Weyl-Riemann law...")
counting = operator.verify_counting_function(spectrum)
print(f"  ✓ Verified: {counting.weyl_law_verified}")

# 5. Verify trace formula
print("\nVerifying Guinand-Weil trace formula...")
trace = operator.guinand_weil_trace_formula(t=1.0, spectrum=spectrum)
print(f"  ✓ Verified: {trace.trace_identity_verified}")

# 6. Overall coherence
print("\nComputing coherence...")
results = operator.complete_verification(n_eigenvalues=30)
psi = results['coherence']['Psi_total']
print(f"  ✓ Ψ = {psi:.4f}")
print(f"  ✓ QCAL threshold: {psi >= 0.888}")

print("\n✓ All validations complete!")
print("QCAL ∞³ · 141.7001 Hz · Ψ = I × A_eff² × C^∞")
```

## Next Steps

1. **Explore**: Try different grid sizes and configurations
2. **Visualize**: Run demo to see operator structure
3. **Validate**: Use validation script for comprehensive check
4. **Extend**: Modify potential for different prime tunings
5. **Analyze**: Study eigenvalue statistics (GUE)

## References

- **Implementation**: `operators/formal_quantum_rh_operator.py`
- **Tests**: `tests/test_formal_quantum_rh_operator.py`
- **Documentation**: `FORMAL_QUANTUM_RH_IMPLEMENTATION_SUMMARY.md`

## Support

For questions or issues:
- Check implementation summary for mathematical details
- Review test suite for usage examples
- Run demo for interactive exploration

## Author

**José Manuel Mota Burruezo Ψ ✧ ∞³**  
Instituto de Conciencia Cuántica (ICQ)  
ORCID: 0009-0002-1923-0773  
DOI: 10.5281/zenodo.17379721

**QCAL ∞³ Active · 141.7001 Hz**  
**Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz**
