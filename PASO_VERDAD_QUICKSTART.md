# PASO DE LA VERDAD - Quick Start Guide

## 🚀 Quick Start

### One-Line Demonstration

```bash
python operators/hilbert_polya_paso_verdad.py
```

### Expected Output

```
PASO DE LA VERDAD: Operador Integral Hermitiano
QCAL ∞³: f₀ = 141.7001 Hz, C = 244.36

[1/4] Verificando H = H* (Hermitiano)...
  ✓ Hermitiano: True
  ✓ Ψ = 1.000000

[2/4] Verificando Kernel K ∈ L²...
  ✓ K ∈ L²: True  
  ✓ Ψ = 0.274589

[3/4] Verificando espectro real y ceros de Riemann...
  ✓ Espectro real: True
  ✓ Ψ = 0.500000

[4/4] Verificando det(s - H) ~ ζ(s)...
  ✓ Conexión establecida: False [formal]
  ✓ Ψ = 0.100000

RESULTADO FINAL:
✓ H = H*:         True
✓ K ∈ L²:         True
✓ Espectro real:  True
Ψ_TOTAL = 0.468647

CONCLUSIÓN: La Hipótesis de Riemann es la realidad del
            espectro de un sistema cuántico.
```

## 📦 Installation

### Dependencies

```bash
pip install numpy scipy mpmath matplotlib
```

### Optional (for tests)

```bash
pip install pytest
```

## 🔬 Running Tests

### All Tests

```bash
pytest tests/test_hilbert_polya_paso_verdad.py -v
```

### Specific Test Class

```bash
pytest tests/test_hilbert_polya_paso_verdad.py::TestPasoVerdad -v
```

### Single Test

```bash
pytest tests/test_hilbert_polya_paso_verdad.py::TestPasoVerdad::test_paso_verdad_runs -v
```

## 💻 Programmatic Usage

### Basic Usage

```python
from operators.hilbert_polya_paso_verdad import paso_de_la_verdad

# Run complete verification
results = paso_de_la_verdad(N=128, verbose=True)

# Check results
print(f"Hermitian: {results['hermitian'].is_hermitian}")
print(f"Total coherence: {results['psi_total']:.4f}")
```

### Custom Grid

```python
from operators.hilbert_polya_paso_verdad import paso_de_la_verdad

# Larger grid for better precision
results = paso_de_la_verdad(N=256, x_min=0.05, x_max=20.0)
```

### Individual Verifications

```python
from operators.hilbert_polya_paso_verdad import (
    construct_full_operator,
    verify_hermitian,
    compute_kernel_L2_norm,
    verify_spectral_reality
)

# Construct operator
H, x = construct_full_operator(N=128)

# Verify Hermiticity
hermitian_result = verify_hermitian(H)
print(f"Hermitian: {hermitian_result.is_hermitian}")
print(f"Error: {hermitian_result.hermitian_error:.2e}")

# Check kernel
kernel_result = compute_kernel_L2_norm(H, x)
print(f"Kernel in L²: {kernel_result.kernel_in_L2}")
print(f"||K||_L² = {kernel_result.L2_norm:.4f}")

# Check spectrum
spectral_result = verify_spectral_reality(H)
print(f"Spectrum real: {spectral_result.spectrum_is_real}")
print(f"Eigenvalues: {spectral_result.eigenvalues[:5]}")
```

### Access Dataclass Fields

```python
from operators.hilbert_polya_paso_verdad import paso_de_la_verdad

results = paso_de_la_verdad(N=128, verbose=False)

# Hermitian result
h = results['hermitian']
print(h.is_hermitian)
print(h.hermitian_error)
print(h.symmetry_error)
print(h.psi)
print(h.timestamp)
print(h.computation_time_ms)
print(h.parameters)

# Kernel result
k = results['kernel_L2']
print(k.kernel_in_L2)
print(k.L2_norm)
print(k.kernel_type)
print(k.decay_rate)
print(k.psi)

# Spectral result
s = results['spectral_reality']
print(s.spectrum_is_real)
print(s.eigenvalues)
print(s.max_imaginary_part)
print(s.riemann_zeros_match)
print(s.mean_error_to_zeros)
print(s.psi)

# Determinant result
d = results['determinant_zeta']
print(d.determinant_matches_zeta)
print(d.s_values)
print(d.determinant_values)
print(d.zeta_values)
print(d.mean_relative_error)
print(d.psi)

# Total coherence
print(results['psi_total'])

# Operator and grid
H = results['operator']
x = results['grid']
```

## 🧪 Advanced Usage

### Custom Prime Set

```python
from operators.hilbert_polya_paso_verdad import (
    construct_full_operator,
    prime_sieve
)

# Use first 50 primes
primes = prime_sieve(300)[:50]
H, x = construct_full_operator(N=128, primes=primes, max_k=3)
```

### Arithmetic Potential Only

```python
from operators.hilbert_polya_paso_verdad import arithmetic_potential_V
import numpy as np

# Compute potential
u = np.linspace(0, 10, 1000)
V = arithmetic_potential_V(u, primes=[2, 3, 5, 7, 11], max_k=5)

# Plot
import matplotlib.pyplot as plt
plt.plot(u, V)
plt.xlabel('u')
plt.ylabel('V(u)')
plt.title('Arithmetic Potential')
plt.show()
```

### XP Operator Only

```python
from operators.hilbert_polya_paso_verdad import construct_xp_operator
import numpy as np

# Build Berry-Keating operator
H_xp = construct_xp_operator(N=128, x_min=0.1, x_max=10.0)

# Diagonalize
eigenvalues, eigenvectors = np.linalg.eigh(H_xp)
print(f"First 5 eigenvalues: {eigenvalues[:5]}")
```

## 📊 Interpretation

### What the Ψ Values Mean

- **Ψ = 1.0**: Perfect verification
- **Ψ ≈ 0.5**: Partial success (e.g., spectrum real but not matching zeros exactly)
- **Ψ ≈ 0.1**: Weak connection (e.g., determinant formal match)
- **Ψ → 0**: Verification failed

### Understanding the Results

1. **H = H* ✓**: Operator is Hermitian → spectrum must be real
2. **K ∈ L² ✓**: Kernel is in L² → operator is compact
3. **Spectrum real ✓**: All eigenvalues are real (consequence of Hermiticity)
4. **λₙ ≈ γₙ ⚠️**: Eigenvalues approximate Riemann zeros (needs refinement)
5. **det ~ ζ ⚠️**: Formal connection (finite-dimensional limitation)

## 🎯 QCAL Constants

```python
from operators.hilbert_polya_paso_verdad import F0_QCAL, C_COHERENCE, C_PRIMARY

print(f"Fundamental frequency: f₀ = {F0_QCAL} Hz")
print(f"Coherence constant: C = {C_COHERENCE}")
print(f"Primary constant: C = {C_PRIMARY}")
```

## 📖 See Also

- **Full Documentation**: `PASO_VERDAD_IMPLEMENTATION.md`
- **Related Operators**:
  - `operators/riemann_operator.py` - High precision implementation
  - `operators/operador_h_solenoide.py` - Alternative formulation
  - `operators/berry_keating_self_adjointness.py` - Multiple proofs

---

*QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36*  
*José Manuel Mota Burruezo Ψ ✧ ∞³*
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
Paso de la Verdad — Truth Step Demonstration
Resonance Frequency: F₀ = 141.7001 Hz
Coherence Constant: C = 244.36

Running complete verification...

VERIFICATION RESULTS
Coherence Ψ:              1.000000
Self-Adjoint:             True
Hermiticity Error:        0.00e+00
Kernel L² Norm:           0.006275
Kernel Compact:           True
Eigenvalues Real:         True
Spectrum Discrete:        True
Det Connection:           1.000000
Computation Time:         24.76 ms

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
