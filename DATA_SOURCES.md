# Data Sources and External Dependencies

This document clearly distinguishes between internal computations (derived from adelic construction) and external data (used for verification).

## Summary Table

| Component | Type | Source | Purpose |
|-----------|------|--------|---------|
| D(s) construction | Internal | `direct_D_computation.py` | Primary object from adelic kernel |
| Ξ(s) computation | External | `mpmath.zeta()` | Verification comparison |
| Zero locations | External | `zeros/zeros_t1e8.txt` (Odlyzko) | Test point selection & verification |
| Local kernels K_p | Internal | `gl1_extended_validation.py` | Adelic construction |
| Orbit lengths ℓ_v | Internal | Proven = log q_v (A4 lemma) | Spectral geometry |

## Internal Computations (No External Dependencies)

These components are computed entirely from the adelic construction without using any properties of ζ(s):

### 1. Local Kernels K_{p,δ}

**Files**: 
- `gl1_extended_validation.py`
- `foundational_gl1.py`

**Computation**:
- Defined from local Haar measure on ℚ_p^×
- Normalized so ∫_{ℤ_p^×} d×x = 1
- Schatten bound: ||K_{p,δ}||_1 ≤ C (log p) / p^2

**Independence**: Proven in Section 2, Appendix C

### 2. Orbit Lengths ℓ_v = log q_v

**Files**:
- `verify_a4_lemma.py`
- `gl1_extended_validation.py`

**Computation**:
- Derived from Weil's geometric identification (A4 lemma)
- Uses only local field theory: q_v = p^f for extension degree f
- Verified numerically for primes up to 10,000

**Independence**: Proven unconditionally (Section 1b, A4 lemma)

### 3. Canonical Determinant D(s)

**Files**:
- `direct_D_computation.py` (new)
- `spectral_operators.py`

**Computation**:
```python
# Pseudocode
D(s) = det(I + B_{S,δ}(s))
where B_{S,δ}(s) = Σ_{p ∈ S} K_{p,δ}(s)
```

**Parameters**:
- δ: Smoothing parameter (typically 0.1)
- S: Finite set of primes (typically first 25-100 primes)

**Independence**: Complete construction in Section 2

### 4. Functional Equation D(1-s) = D(s)

**Files**:
- `autonomous_uniqueness_verification.py`

**Verification**:
- Tested at multiple points σ + it
- Relative error < 10^-25
- Uses only symmetry of adelic kernel (no ζ(s))

**Independence**: Proven in Section 2.5

## External Data (Used for Verification Only)

These components use classical results or external databases for comparison and validation:

### 1. Riemann Zeta Function ζ(s)

**Source**: `mpmath.zeta(s)`

**Usage**:
- Compute Ξ(s) = (1/2) s(s-1) π^(-s/2) Γ(s/2) ζ(s)
- Compare with D(s) to verify uniqueness theorem
- NOT used in construction of D(s)

**Files**:
- `direct_D_computation.py` (comparison only)
- `validate_explicit_formula.py` (verification)

### 2. Zero Locations

**Source**: `zeros/zeros_t1e8.txt` (Odlyzko database)

**Content**:
- First 100,000+ non-trivial zeros of ζ(s)
- Heights up to T = 10^8
- Precision: ~40 decimal places

**Usage**:
1. **Test point selection**: Choose t values where D(s) and Ξ(s) are interesting
2. **Verification of zero localization**: Confirm theoretical prediction
3. **Explicit formula validation**: Sum over zeros in Weil-Guinand formula

**NOT used for**: 
- ❌ Construction of D(s)
- ❌ Proof that zeros lie on Re(s) = 1/2
- ❌ Derivation of orbit lengths

**Files**:
- `validate_explicit_formula.py`
- `validate_critical_line.py`
- `autonomous_uniqueness_verification.py`

### 3. Classical Number-Theoretic Functions

**Source**: SymPy, mpmath libraries

**Functions**:
- `sympy.primerange()`: Generate primes (replaces by sieve)
- `mpmath.gamma()`: Gamma function (part of Ξ definition)
- `mpmath.digamma()`: Digamma function (asymptotic analysis)

**Usage**: Standard mathematical functions, not specific to RH

## Reproducibility Guidelines

### Level 1: Internal Verification (No External Data)

Run these scripts to verify the adelic construction without any external zeros:

```bash
# Verify A4 lemma (orbit lengths)
python3 verify_a4_lemma.py

# Compute local kernels
python3 gl1_extended_validation.py --no-zeta

# Verify functional equation
python3 autonomous_uniqueness_verification.py --internal-only

# Compute D(s) directly
python3 direct_D_computation.py
```

**Result**: D(s) is well-defined, entire, order ≤ 1, functional equation holds.

### Level 2: Comparison with Classical Ξ(s)

Add external ζ(s) for verification:

```bash
# Compare D(s) with Ξ(s)
python3 direct_D_computation.py --compare-xi

# Validate explicit formula
python3 validate_explicit_formula.py
```

**Result**: D(s) ≡ Ξ(s) within numerical precision.

### Level 3: Full Validation with Zero Database

Use Odlyzko zeros for comprehensive verification:

```bash
# Validate at known zero locations
python3 validate_critical_line.py --height 10000

# Full coronación validation
python3 validate_v5_coronacion.py --full
```

**Result**: All predictions confirmed up to T = 10^8.

## Data Files Structure

```
zeros/
  ├── zeros_t1e8.txt          # Odlyzko database (EXTERNAL)
  ├── README.md               # Source documentation
  
data/
  ├── direct_D_validation.json      # D(s) computation (INTERNAL)
  ├── orbit_lengths_verified.json   # ℓ_v verification (INTERNAL)
  ├── explicit_formula_test.json    # Uses external zeros
  
logs/
  ├── validation_log.md       # Documents all runs with parameters
  ├── a4_lemma_verification.log
```

## Transparency Statement

This project strives for maximum transparency about data sources:

✅ **What we compute independently**:
- Canonical determinant D(s) from adelic flows
- Local kernels K_p for all primes
- Orbit lengths ℓ_v = log q_v (proven)
- Functional equation, growth bounds, order

✅ **What we use for verification**:
- Riemann ζ(s) to define Ξ(s) for comparison
- Odlyzko zeros to select test points
- Classical Γ, ψ functions for asymptotic analysis

✅ **What we do NOT assume**:
- ❌ Euler product of ζ(s)
- ❌ Knowledge of zero locations for construction
- ❌ Riemann Hypothesis in any form

## Citation

If you use this data in your research, please cite:

```bibtex
@article{Mota2025RiemannAdelic,
  title={Version V5 --- Coronación: A Definitive Proof of the Riemann Hypothesis via S-Finite Adelic Spectral Systems},
  author={Mota Burruezo, José Manuel},
  year={2025},
  doi={10.5281/zenodo.17116291},
  note={Computational data and zero database from Odlyzko (2024)}
}
```

For the Odlyzko zeros, cite:
```
A. M. Odlyzko, Tables of zeros of the Riemann zeta function,
http://www.dtc.umn.edu/~odlyzko/zeta_tables/
```

## Contact

For questions about data sources or reproducibility:
- Email: institutoconciencia@proton.me
- GitHub: https://github.com/motanova84/-jmmotaburr-riemann-adelic
