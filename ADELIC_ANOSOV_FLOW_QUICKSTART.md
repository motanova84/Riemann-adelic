# Adelic Anosov Flow - Quick Reference

## TL;DR

**El flujo adélico es Anosov porque la métrica no se impone, sino que emerge.**

The metric emerges from the idelic action, creating natural hyperbolic dynamics that connect to the Selberg trace formula and Riemann zeta function.

## Quick Start

```python
from operators.adelic_anosov_flow import AdelicAnosovFlow

# Create and validate
flow = AdelicAnosovFlow()
verification = flow.verify_hyperbolicity()

# Is it Anosov?
print(verification['is_anosov'])  # True
print(verification['metric_emergent'])  # True
```

## Key Concepts

### 1. Idelic Space
```
X = A_Q^1 / Q*
```
- Unit ideles modulo rationals
- Product: Archimedean × p-adic

### 2. Dilation Flow
```
φ_t(x) = e^t x
```
- Expansive in real direction: `|e^t|_∞ = e^t`
- Contractive in p-adic frame: compression

### 3. Anosov Decomposition
```
T_x X = E^0 ⊕ E^u ⊕ E^s
```
- **E^0**: Flow direction
- **E^u**: Unstable (expansion by `e^t`)
- **E^s**: Stable (contraction by `e^(-t)`)

### 4. Closed Orbits
```
qx = φ_t(x) ⟹ q = e^t = p^k
```
- Orbits when `e^t` is rational
- Weight: `ln p / p^(k/2)`

### 5. Selberg Trace
```
Tr(e^(-tH)) = Σ_orbits weight × e^(-t·length)
```
- Emerges from Poisson identity
- Poles at `k ln p`

## Essential Methods

### Create Flow
```python
flow = AdelicAnosovFlow(
    primes=[2, 3, 5, 7, 11],  # p-adic components
    t_max=5.0,                 # time range
    n_points=100               # discretization
)
```

### Archimedean Norm (Expansive)
```python
norm = flow.archimedean_norm(x=2.5, t=1.0)
# Returns: e^t × |x|
```

### p-adic Norm (Contractive)
```python
norm = flow.p_adic_norm(x=8, p=2)
# Returns: p^(-v_p(x)) where v_p(x) = 3
# Result: 2^(-3) = 0.125
```

### Anosov Decomposition
```python
decomp = flow.anosov_decomposition(x=1.0, t=1.0)
# Returns: {'E0': ..., 'E_unstable': ..., 'E_stable': ...}
```

### Find Closed Orbits
```python
orbits = flow.closed_orbits(t_max=10.0)
# Each orbit has: prime, power, time, q, weight, ln_p
```

### Compute Selberg Trace
```python
trace = flow.selberg_trace(t=1.0)
# Returns: trace value at time t
```

### Verify Hyperbolicity
```python
verification = flow.verify_hyperbolicity()
# Returns: {
#   'is_anosov': True,
#   'lyapunov_gap': 1.0,
#   'metric_emergent': True
# }
```

### Lyapunov Exponents
```python
lyap = flow.lyapunov_exponents()
# Returns: {
#   'unstable': +1.0,   # expansion
#   'stable': -1.0,     # contraction  
#   'neutral': 0.0      # flow direction
# }
```

### Connection to Zeta
```python
conn = flow.connection_to_zeta(s=0.5+14.134725j)
# Returns: poles, poisson_value, pole_density
```

## Validation

Run complete validation:
```bash
python validate_adelic_anosov_flow.py
```

Expected output:
```
✓ El flujo adélico es Anosov
✓ La métrica emerge del espacio
✓ La fórmula de Selberg es exacta
✓ Los polos coinciden con ζ'(s)/ζ(s)
```

## Key Results

### Hyperbolicity
- ✓ Lyapunov gap: 1.0 (uniform)
- ✓ Anosov: True
- ✓ Metric emergent: True

### Volume Preservation
```python
expansion × contraction = 1
e^t × e^(-t) = 1
```

### Closed Orbits (first 5)
| Prime | Power | Time   | q    | Weight  |
|-------|-------|--------|------|---------|
| 2     | 1     | 0.693  | 2    | 0.4901  |
| 2     | 2     | 1.386  | 4    | 0.3466  |
| 2     | 3     | 2.079  | 8    | 0.2451  |
| 2     | 4     | 2.773  | 16   | 0.1733  |
| 2     | 5     | 3.466  | 32   | 0.1225  |

### Selberg Trace Decay
| t   | Tr(e^(-tH)) |
|-----|-------------|
| 0.5 | 2.422       |
| 1.0 | 1.034       |
| 1.5 | 0.511       |
| 2.0 | 0.279       |
| 3.0 | 0.100       |
| 5.0 | 0.019       |

## Mathematical Properties

### Why It's Anosov

1. **Uniform hyperbolicity**
   - Lyapunov exponents: +1, -1
   - Gap from zero: 1.0

2. **Metric emerges**
   - From idelic structure
   - Not externally imposed

3. **Product structure**
   - R (expansive) × Compact (contractive)
   - Natural hyperbolic geometry

4. **Trace formula exact**
   - Poisson identity
   - Closed orbits from rationality

### Connection to RH

- Poles at `k ln p`
- Match `ζ'(s)/ζ(s)`
- Hyperbolic dynamics → spectral theory

## Files

- **Implementation**: `operators/adelic_anosov_flow.py`
- **Tests**: `tests/test_adelic_anosov_flow.py`
- **Validation**: `validate_adelic_anosov_flow.py`
- **Results**: `data/adelic_anosov_flow_validation.json`
- **Documentation**: `ADELIC_ANOSOV_FLOW_IMPLEMENTATION.md`

## QCAL Integration

- Frequency: **141.7001 Hz** (f₀)
- Coherence: **C = 244.36**
- Threshold: **κ_Π = 2.5773**
- Signature: **Ψ = I × A_eff² × C^∞**

## References

- **DOI**: 10.5281/zenodo.17379721
- **ORCID**: 0009-0002-1923-0773
- **Author**: José Manuel Mota Burruezo Ψ ✧ ∞³
- **Institution**: Instituto de Conciencia Cuántica (ICQ)
- **Date**: February 2026

---

**La hiperbolicidad es efectiva:**
- Expansión en dirección arquimediana (real)
- Contracción en direcciones p-ádicas
- El espacio es producto: R × Compacto
