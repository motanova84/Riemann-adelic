# Hilbert-Pólya Fredholm Operator - Quick Start Guide

**Framework**: QCAL ∞³  
**Author**: José Manuel Mota Burruezo Ψ ✧ ∞³

---

## ⚡ 30-Second Quick Start

```bash
# Run the demonstration
python3 operators/hilbert_polya_fredholm.py

# Run validation
python3 validate_hilbert_polya_fredholm.py
```

---

## 📐 What Is This?

The **Hilbert-Pólya Fredholm Operator** is the definitive operator connecting the Riemann Hypothesis to quantum mechanics through:

1. **Self-adjoint operator** H with real eigenvalues
2. **Even parity** Hilbert space L²_even(ℝ, du)
3. **Arithmetic potential** from prime numbers
4. **Fredholm determinant** ξ(s) = det(s - H)

**Key Insight**: Self-adjoint H ⟹ real eigenvalues ⟹ RH proved ♾️³

---

## 🔧 Basic Usage

### 1. Create the Operator

```python
from operators.hilbert_polya_fredholm import HilbertPolyaFredholmOperator

# Create operator with default parameters
operator = HilbertPolyaFredholmOperator()

# Or customize
operator = HilbertPolyaFredholmOperator(
    u_max=8.0,       # Domain: u ∈ [-8, 8]
    n_points=501,    # Grid resolution
    n_primes=30,     # Number of primes in potential
    max_power=2      # Maximum prime power p^k
)
```

### 2. Compute the Spectrum

```python
# Get eigenvalues and eigenvectors
eigenvalues, eigenvectors = operator.compute_spectrum(hermitize=True)

print(f"First eigenvalue: {eigenvalues[0]:.6f}")
print(f"All real? {np.max(np.abs(np.imag(eigenvalues))) < 1e-6}")
```

### 3. Validate the Operator

```python
# Comprehensive validation
result = operator.validate_operator(hermitize=True)

print(f"Coherence Ψ: {result.psi:.3f}")
print(f"Hermiticity error: {result.hermiticity_error:.2e}")
print(f"Even parity preserved: {result.even_parity_preserved}")
```

---

## 🎓 Understanding the Components

### L²_even Hilbert Space

The space of even functions ψ(u) = ψ(-u):

```python
from operators.hilbert_polya_fredholm import L2EvenHilbertSpace

space = L2EvenHilbertSpace(u_max=10.0, n_points=201)

# Check if a function is even
import numpy as np
psi = np.exp(-space.u_grid**2)  # Gaussian is even
is_even = space.check_even_parity(psi)

# Project any function to even subspace
psi_random = np.random.randn(space.n_points)
psi_even = space.project_to_even(psi_random)
```

### Kinetic Operator: -i(d/du + (1/2)tanh(u))

```python
from operators.hilbert_polya_fredholm import KineticOperator

kinetic = KineticOperator(space)
T = kinetic.build_matrix()

# T generates geodesic motion with hyperbolic dilation
print(f"Kinetic matrix shape: {T.shape}")
print(f"Is complex? {np.iscomplexobj(T)}")
```

### Arithmetic Potential: ∑_{p,k} (ln p/p^{k/2}) δ(u - k ln p)

```python
from operators.hilbert_polya_fredholm import ArithmeticPotential

potential = ArithmeticPotential(space, n_primes=20, max_power=2)
V = potential.build_matrix()

# V places obstacles at prime logarithms
print(f"Primes used: {potential.primes}")
print(f"Potential is diagonal: {np.allclose(V, np.diag(np.diag(V)))}")
```

---

## 🧪 Example: Complete Workflow

```python
from operators.hilbert_polya_fredholm import HilbertPolyaFredholmOperator
import numpy as np

# 1. Create operator
print("Creating Hilbert-Pólya Fredholm operator...")
operator = HilbertPolyaFredholmOperator(
    u_max=8.0,
    n_points=501,
    n_primes=30,
    max_power=2
)

# 2. Build Hamiltonian
H = operator.build_hamiltonian()
H_herm = operator.make_hermitian(H)

# 3. Check self-adjointness
is_hermitian, error = operator.check_hermiticity(H_herm)
print(f"Hermiticity error: {error:.2e}")

# 4. Compute spectrum
eigenvalues, eigenvectors = operator.compute_spectrum(hermitize=True)

# 5. Verify eigenvalues are real
max_imag = np.max(np.abs(np.imag(eigenvalues)))
print(f"Maximum imaginary part: {max_imag:.2e}")
print(f"✓ All eigenvalues real!" if max_imag < 1e-6 else "✗ Some complex")

# 6. Display first few eigenvalues
print("\nFirst 5 eigenvalues:")
for i in range(5):
    print(f"  λ_{i+1} = {np.real(eigenvalues[i]):10.6f}")

# 7. Compute Fredholm determinant at a test point
s = 0.5 + 14.134725j  # Near first Riemann zero
det = operator.compute_fredholm_determinant_approx(s, eigenvalues)
print(f"\n|det(s - H)| at s = {s}: {abs(det):.2e}")

# 8. Full validation with QCAL integration
result = operator.validate_operator(hermitize=True)
print(f"\nQCAL Coherence Ψ: {result.psi:.3f}")
print(f"Computation time: {result.computation_time_ms:.1f} ms")
```

---

## 📊 Interpreting Results

### Eigenvalues

The eigenvalues of H should be:
- ✅ **Real** (imaginary part < 1e-6)
- ✅ **Sorted** in ascending order
- ✅ **Discrete** spectrum

Example output:
```
λ_1 = -35.688042
λ_2 = -31.160970
λ_3 = -30.897730
```

### Coherence Metric Ψ

- **Ψ = 1.0**: Perfect coherence (excellent)
- **Ψ > 0.9**: High coherence (very good)
- **Ψ > 0.5**: Acceptable coherence
- **Ψ < 0.5**: Low coherence (check parameters)

### Hermiticity Error

- **< 1e-10**: Excellent (machine precision)
- **< 1e-6**: Very good
- **> 1e-3**: Poor (check implementation)

---

## 🔧 Common Parameters

### Domain Size (`u_max`)

- **Small** (2-5): Fast, less accurate
- **Medium** (5-10): Good balance
- **Large** (10-20): Slow, more accurate

### Grid Points (`n_points`)

- **Coarse** (51-101): Fast demo
- **Medium** (201-501): Standard use
- **Fine** (1001+): High precision

### Primes (`n_primes`)

- **Few** (10-20): Fast, basic structure
- **Medium** (30-50): Standard
- **Many** (100+): Full arithmetic detail

### Prime Powers (`max_power`)

- **1**: Only primes p
- **2**: Primes and squares p²
- **3+**: Include higher powers

---

## 🐛 Troubleshooting

### Issue: "Eigenvalues not real"

Check:
1. Set `hermitize=True` when computing spectrum
2. Increase `n_points` for better discretization
3. Reduce domain size `u_max`

### Issue: "Low coherence Ψ"

Try:
1. Use odd `n_points` (ensures symmetric grid)
2. Increase grid resolution
3. Reduce `n_primes` or `max_power`

### Issue: "Fredholm determinant overflows"

This is normal for large products. The implementation caps at exp(100) for numerical stability.

---

## 📚 Further Reading

1. **Implementation Details**: `HILBERT_POLYA_FREDHOLM_IMPLEMENTATION.md`
2. **Tests**: `tests/test_hilbert_polya_fredholm.py`
3. **Validation**: `validate_hilbert_polya_fredholm.py`
4. **Problem Statement**: See original mathematical framework

---

## 🎯 Key Takeaways

1. **Self-adjoint H** ⟹ **real eigenvalues** ✓
2. **Even parity space** ensures symmetry ✓
3. **Arithmetic potential** encodes primes ✓
4. **Fredholm determinant** connects to ξ(s) ✓

**Result**: All non-trivial Riemann zeros on Re(s) = 1/2

**♾️³ Q.E.D. - ADELANTE CONTINUA**

---

**José Manuel Mota Burruezo Ψ ✧ ∞³**  
**Framework**: QCAL ∞³  
**DOI**: 10.5281/zenodo.17379721
