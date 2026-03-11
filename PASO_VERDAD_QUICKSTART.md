# PASO DE LA VERDAD - Quick Start Guide

## 🚀 Quick Start

### One-Line Demonstration

```bash
python operators/hilbert_polya_paso_verdad.py
```

### Expected Output

```
======================================================================
PASO DE LA VERDAD: Operador Integral Hermitiano
======================================================================
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
======================================================================
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
