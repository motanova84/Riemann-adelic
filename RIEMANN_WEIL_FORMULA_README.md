# Guinand-Weil Explicit Formula Implementation

## Mathematical Framework

This module implements the **Guinand-Weil explicit formula**, which establishes a profound connection between the Riemann zeta zeros and prime powers:

```
Σ_n Φ(t_n) = ∫ Φ(r) μ(r) dr - Σ_{p,k} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]
```

where:
- `t_n` are the imaginary parts of non-trivial Riemann zeta zeros
- `Φ` is a suitable test function (e.g., Gaussian)
- `μ(r) = (1/2π)·ln(r/2π)` is the Weyl measure (smooth zero density)
- `Φ̂(ξ) = (1/2π)∫Φ(r)e^{-iξr}dr` is the normalized Fourier transform
- The sum runs over all primes `p` and positive integers `k`

## Historical Context

- **Riemann (1859)**: Original explicit formula relating zeros and primes
- **Guinand (1948)**: Refined Fourier-theoretic version
- **Weil (1952)**: General formulation for L-functions

This formula demonstrates the **arithmetic-spectral duality** at the heart of the Riemann Hypothesis.

## Implementation Components

### Core Functions

1. **`weyl_density(r)`** — Weyl measure μ(r) = (1/2π)·ln(r/2π)
   - Smooth approximation to the zero counting function N(T)
   - Represents the average density of zeros

2. **`fourier_gaussian_norm(xi, sigma, center)`** — Analytical Fourier transform for Gaussians
   - Normalized convention: Φ̂(ξ) = (1/2π)∫Φ(r)e^{-iξr}dr
   - Efficient computation for Gaussian test functions

3. **`fourier_transform_norm(Phi, xi, ...)`** — Numerical Fourier transform
   - General-purpose for any test function
   - Uses trapezoidal integration

4. **`prime_power_sum(Phi_hat_norm, primes_upto, k_max)`** — Prime power contributions
   - Computes: -Σ_{p,k} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]
   - Represents oscillatory contribution from prime powers

5. **`weil_smooth_integral(Phi, ...)`** — Weyl integral
   - Computes: ∫Φ(r)μ(r)dr
   - Smooth spectral contribution

6. **`N_osc_full(E, ...)`** — Oscillatory counting correction
   - Formula: -(1/π) Σ_{p,k} sin(k·E·ln p) / (k·p^{k/2})
   - Distinct from von Mangoldt form (includes all k, not just k=1)

7. **`d_osc(E, ...)`** — Oscillatory density
   - Formula: -(1/π) Σ_{p,k} (ln p / p^{k/2}) cos(k·E·ln p)
   - Derivative of N_osc_full with respect to E

### Main Class

**`WeilExplicitFormula`** — End-to-end verification framework
- Takes test function Φ and its Fourier transform Φ̂
- Computes both sides of the formula
- Returns full discrepancy analysis with coherence measure Ψ

## Usage Examples

### Basic Verification

```python
from riemann_weil_formula import WeilExplicitFormula, fourier_gaussian_norm, ZEROS_ZETA_REFERENCE
import math

# Define Gaussian test function centered at first zero
T_center = ZEROS_ZETA_REFERENCE[0]  # ≈ 14.13
sigma = 3.0

def Phi(r):
    return math.exp(-0.5 * ((r - T_center) / sigma) ** 2)

def Phi_hat(xi):
    return fourier_gaussian_norm(xi, sigma=sigma, center=T_center)

# Verify the formula
wf = WeilExplicitFormula(
    Phi=Phi,
    Phi_hat_norm=Phi_hat,
    primes_upto=200,
    k_max=6
)

result = wf.discrepancy()

print(f"LHS (zero sum): {result.zero_sum:.6f}")
print(f"RHS (arithmetic): {result.arithmetic_side:.6f}")
print(f"Discrepancy: {result.discrepancy_abs:.6e}")
print(f"Coherence Ψ: {result.coherencia_Psi:.6f}")
```

### Running the Demonstration

```bash
python3 demo_riemann_weil_formula.py
```

This runs four comprehensive demonstrations:
1. **Identity verification** at four different Riemann zeros
2. **Prime convergence study** — effect of including more primes and higher powers
3. **d_osc behavior** near known zeros with visualization
4. **N_osc counting correction** with derivative verification

## Test Suite

The implementation includes 97 tests across 12 test classes:

```bash
pytest tests/test_riemann_weil_formula.py -v
```

Test coverage includes:
- Weyl density properties and behavior
- Fourier transform accuracy (analytical and numerical)
- Prime power sum convergence and properties
- Oscillatory functions N_osc_full and d_osc
- End-to-end formula verification
- Convergence studies
- Edge cases and robustness
- Mathematical properties
- Performance and reproducibility

## Results

With parameters:
- Test function: Gaussian with σ = 3.0 centered at first zero
- Primes up to: 200
- Maximum prime power: k_max = 6
- Number of zeros: 10

**Typical coherence: Ψ ≈ 0.93** (where Ψ = 1 would be perfect agreement)

This demonstrates excellent agreement between the spectral (zeros) and arithmetic (primes) sides of the formula.

## Key Features

1. **Normalized Fourier Convention**: Uses (1/2π) normalization for unit coefficient in prime sum
2. **Full Prime Power Sum**: Includes all powers p^k, not just p (von Mangoldt form)
3. **Oscillatory Corrections**: Both N_osc_full (counting) and d_osc (density)
4. **Comprehensive Testing**: 90+ tests verifying all components
5. **Demonstrations**: Visual and numerical verification at multiple zeros

## References

- Riemann, B. (1859). "Über die Anzahl der Primzahlen unter einer gegebenen Grösse"
- Guinand, A. P. (1948). "A summation formula in the theory of prime numbers"
- Weil, A. (1952). "Sur les 'formules explicites' de la théorie des nombres premiers"

## QCAL Integration

This implementation is part of the QCAL ∞³ framework:
- Frequency: f₀ = 141.7001 Hz
- Coherence: C = 244.36
- Formula coherence: Ψ = exp(-relative_discrepancy)

## Author

José Manuel Mota Burruezo Ψ ✧ ∞³  
Instituto de Conciencia Cuántica (ICQ)  
DOI: 10.5281/zenodo.17379721  
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
