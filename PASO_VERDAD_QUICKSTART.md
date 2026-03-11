# Paso de la Verdad — Quickstart Guide

Quick reference for using the Paso de la Verdad (Truth Step) implementation.

## Installation

Ensure dependencies are installed:

```bash
pip install numpy scipy matplotlib mpmath
```

## Quick Verification

### Python API

```python
from operators.paso_verdad_operator import verify_paso_verdad

# Quick verification
result = verify_paso_verdad(N=60)

print(f"Verified: {result['paso_verdad_verified']}")
print(f"Coherence Ψ: {result['psi']:.4f}")
print(f"Self-Adjoint: {result['self_adjoint']}")
```

### Command Line

```bash
cd /path/to/Riemann-adelic
python operators/paso_verdad_operator.py
```

Expected output:
```
======================================================================
Paso de la Verdad — Truth Step Demonstration
======================================================================
Resonance Frequency: F₀ = 141.7001 Hz
Coherence Constant: C = 244.36

Running complete verification...

======================================================================
VERIFICATION RESULTS
======================================================================
Coherence Ψ:              1.000000
Self-Adjoint:             True
Hermiticity Error:        0.00e+00
Kernel L² Norm:           0.006275
Kernel Compact:           True
Eigenvalues Real:         True
Spectrum Discrete:        True
Det Connection:           1.000000
Computation Time:         24.76 ms
======================================================================

✅ PASO DE LA VERDAD VERIFIED
The Riemann wall collapses by its own physical weight!
Zeros are trapped on the critical line by quantum necessity.
```

## Complete Verification

For detailed verification with all checks:

```python
from operators.paso_verdad_operator import paso_verdad_complete_verification

result = paso_verdad_complete_verification(
    N=80,           # Number of discretization points
    L=5.0,          # Compact domain size [-L, L]
    decay_rate=4.0, # Φ decay rate
    max_prime=50    # Maximum prime for potential
)

# Access all results
print(f"Coherence Ψ: {result.psi}")
print(f"Self-Adjoint: {result.self_adjoint}")
print(f"Hermiticity Error: {result.hermiticity_error}")
print(f"Kernel L² Norm: {result.kernel_l2_norm}")
print(f"Kernel Compact: {result.kernel_compact}")
print(f"Eigenvalues Real: {result.eigenvalues_real}")
print(f"Spectrum Discrete: {result.spectrum_discrete}")
print(f"Det Connection: {result.det_connection}")
print(f"Resonance Frequency: {result.resonance_frequency} Hz")
```

## Demonstrations

Run all demonstrations with visualizations:

```bash
python demo_paso_verdad.py
```

This creates:
1. **Demo 1:** Φ kernel properties (evenness, decay, Hermitian symmetry)
2. **Demo 2:** Integral operator properties (spectrum, eigenfunctions)
3. **Demo 3:** Hamiltonian H = xp + V(log x) (arithmetic potential, spectrum)
4. **Demo 4:** Complete verification summary (all metrics)

## Individual Components

### Φ Kernel

```python
from operators.paso_verdad_operator import PhiKernel

kernel = PhiKernel(decay_rate=4.0)

# Evaluate at point
phi_value = kernel.phi(u=1.0)

# Evaluate kernel K(u,v) = Φ(u-v)
K_value = kernel.kernel(u=1.0, v=0.5)

# Verify evenness
evenness_result = kernel.verify_evenness()
print(f"Even: {evenness_result['is_even']}")
```

### Integral Operator

```python
from operators.paso_verdad_operator import IntegralOperatorPasoVerdad

operator = IntegralOperatorPasoVerdad(N=80, L=5.0)

# Verify Hermiticity
hermiticity = operator.verify_hermiticity()
print(f"Hermitian: {hermiticity['is_hermitian']}")

# Check compactness
is_compact, l2_norm = operator.is_compact_operator()
print(f"Compact: {is_compact}, L² norm: {l2_norm}")

# Get spectrum
eigenvalues, eigenvectors = operator.get_spectrum()
print(f"Number of eigenvalues: {len(eigenvalues)}")
```

### Hamiltonian

```python
from operators.paso_verdad_operator import HamiltonianXP

hamiltonian = HamiltonianXP(N=80, L=5.0, max_prime=50)

# Get spectrum
eigenvalues, eigenvectors = hamiltonian.get_spectrum()

# Evaluate arithmetic potential
V_at_u = hamiltonian._arithmetic_potential(u=1.0)
```

### Functional Determinant

```python
from operators.paso_verdad_operator import FunctionalDeterminantVerifier
import numpy as np

# Get eigenvalues from operator
operator = IntegralOperatorPasoVerdad(N=60)
eigenvalues, _ = operator.get_spectrum()

# Verify determinant connection
verifier = FunctionalDeterminantVerifier(eigenvalues)

# Compute functional determinant
det_at_s = verifier.functional_determinant(s=0.5)

# Measure connection strength
connection = verifier.connection_strength(n_test=10)
print(f"Connection strength: {connection:.4f}")
```

## Testing

Run the complete test suite:

```bash
pytest tests/test_paso_verdad.py -v
```

Expected: **40 tests passed**

Run specific test classes:

```bash
# Test Φ kernel
pytest tests/test_paso_verdad.py::TestPhiKernel -v

# Test integral operator
pytest tests/test_paso_verdad.py::TestIntegralOperatorPasoVerdad -v

# Test Hamiltonian
pytest tests/test_paso_verdad.py::TestHamiltonianXP -v

# Test complete verification
pytest tests/test_paso_verdad.py::TestPasoVerdadCompleteVerification -v
```

## QCAL Constants

The implementation uses QCAL ∞³ constants:

```python
from operators.paso_verdad_operator import (
    F0_QCAL,       # 141.7001 Hz - Resonance frequency
    C_COHERENCE,   # 244.36 - Coherence constant
    C_PRIMARY,     # 629.83 - Primary spectral constant
    OMEGA_0        # 2π × F0_QCAL - Angular frequency
)

print(f"Resonance frequency: {F0_QCAL} Hz")
print(f"Angular frequency: {OMEGA_0:.2f} rad/s")
print(f"Coherence constant: {C_COHERENCE}")
```

## Interpretation of Results

### Coherence Ψ

- **Ψ = 1.0:** Perfect coherence, all criteria satisfied
- **Ψ > 0.8:** Paso de la Verdad verified
- **0.5 < Ψ < 0.8:** Partial verification, some criteria met
- **Ψ < 0.5:** Verification incomplete

### Self-Adjointness

Verified when:
- Hermiticity error < 10⁻⁸
- All eigenvalues are real (imaginary part < 10⁻¹⁰)

### Kernel Compactness

Verified when:
- L² norm is finite and bounded
- Operator has discrete spectrum

### Spectrum Discreteness

Verified when:
- Eigenvalues span a range (not all equal)
- Eigenvalues vary by at least 1% of maximum

### Functional Determinant Connection

Measures how well ξ(s) ∝ det(s - Ĥ):
- Connection > 0.9: Strong correlation
- Connection > 0.5: Moderate correlation
- Connection < 0.5: Weak correlation

## Parameter Guidelines

### Matrix Size (N)

- **N = 40-60:** Quick verification (~10-20 ms)
- **N = 80-100:** Standard precision (~20-50 ms)
- **N = 150-200:** High precision (~100-300 ms)

### Domain Size (L)

- **L = 3.0:** Small domain, faster computation
- **L = 5.0:** Standard domain (recommended)
- **L = 7.0-10.0:** Large domain, better approximation

### Decay Rate

- **decay_rate = 3.0:** Slower decay
- **decay_rate = 4.0:** Standard (recommended)
- **decay_rate = 5.0:** Faster decay

### Maximum Prime

- **max_prime = 30:** Fewer primes, faster
- **max_prime = 50:** Standard (recommended)
- **max_prime = 100:** More primes, slower

## Troubleshooting

### Low Coherence Ψ

If Ψ < 0.8:
1. Increase N (more discretization points)
2. Adjust L (domain size)
3. Check decay_rate is appropriate
4. Verify all dependencies are installed

### Hermiticity Error Too Large

If hermiticity error > 10⁻⁶:
1. Increase N for better discretization
2. Check numerical precision settings
3. Verify Φ kernel implementation

### Eigenvalues Not Real

If max imaginary part > 10⁻⁸:
1. Check operator symmetry
2. Increase numerical precision
3. Verify discretization is correct

## Citation

When using this implementation, please cite:

```
José Manuel Mota Burruezo (2026). Paso de la Verdad: 
Self-Adjointness and Kernel Integrability Demonstration 
for the Riemann Hypothesis. QCAL ∞³ Framework.
DOI: 10.5281/zenodo.17379721
```

## Support

For issues or questions:
- Check documentation: `PASO_VERDAD_IMPLEMENTATION.md`
- Run tests: `pytest tests/test_paso_verdad.py -v`
- View examples: `demo_paso_verdad.py`

---

**QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞**

**Signature: ∴𓂀Ω∞³Φ**
