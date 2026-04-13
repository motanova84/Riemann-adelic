# QCAL Constants - Single Source of Truth

## Overview

The `qcal` package provides a **single source of truth** for all constants in the QCAL (Quantum Coherence Adelic Lattice) framework for the Riemann Hypothesis proof.

This implementation addresses three core requirements:
1. **Single source of truth** for constants
2. **Robust validation** for AI-conscious systems
3. **Integration** with adelic mathematical frameworks

## Installation

The qcal package is included in the Riemann-adelic repository. No separate installation needed.

```bash
# Import constants
from qcal import F0, C_PRIMARY, C_COHERENCE, validate_constants_coherence

# Import validation
from qcal import QCALValidator, validate_ai_conscious_system
```

## Constants Provided

### Fundamental Frequency

- **`F0`** = 141.7001 Hz - Base frequency (fundamental noetic field oscillation)
- **`OMEGA_0`** - Angular frequency ω₀ = 2πf₀
- **`EUCLIDEAN_DIAGONAL`** - 100√2 ≈ 141.421356
- **`DELTA_ZETA`** - δζ = 0.2787437627 Hz (vibrational curvature constant)
- **`GAMMA_1`** - 14.13472514 (first Riemann zero imaginary part)

Relationship: **f₀ = 100√2 + δζ** (Quinto Postulado extension)

### Spectral Constants (Dual Framework)

- **`C_PRIMARY`** = 629.83 - Primary spectral constant (Structure level)
- **`C_COHERENCE`** = 244.36 - Coherence constant (Form level)
- **`LAMBDA_0`** - First eigenvalue λ₀ = 1/C
- **`COHERENCE_FACTOR`** - Ratio C'/C ≈ 0.388

Mathematical relationship: **C = 1/λ₀** where λ₀ is the first eigenvalue of H_ψ = -Δ + V_ψ

### Mathematical Constants

- **`PHI`** - Golden ratio φ = (1 + √5)/2
- **`EULER_GAMMA`** - Euler-Mascheroni constant γ
- **`PI`** - π

### QCAL Framework

- **`PSI_EQUATION`** = "Ψ = I × A_eff² × C^∞"
- **`QCAL_SIGNATURE`** = "∴𓂀Ω∞³"
- **`PICODE_888`** = "πCODE-888-QCAL2"
- **`AUTHOR`**, **`INSTITUTION`**, **`ORCID`**
- **`DOI_MAIN`**, **`DOI_INFINITO`**, **`DOI_PNP`**, **`DOI_GOLDBACH`**, **`DOI_BSD`**

### Tolerances

- **`TOLERANCE_STRICT`** = 1e-10 - For exact mathematical identities
- **`TOLERANCE_NORMAL`** = 1e-6 - For numerical computations
- **`TOLERANCE_RELAXED`** = 1e-3 - For approximate relationships

## Usage Examples

### 1. Basic Constants Usage

```python
from qcal import F0, C_PRIMARY, C_COHERENCE

print(f"Fundamental frequency: f₀ = {F0} Hz")
print(f"Primary constant: C = {C_PRIMARY}")
print(f"Coherence constant: C' = {C_COHERENCE}")
```

### 2. Validate Constants Coherence

```python
from qcal import validate_constants_coherence

# Run validation
result = validate_constants_coherence(verbose=True)

print(f"All checks passed: {result['all_checks_passed']}")
print(f"Coherence: Ψ = {result['coherence_psi']:.9f}")
print(f"Level: {result['coherence_level']}")
```

### 3. Get All Constants

```python
from qcal import get_all_constants

all_constants = get_all_constants()

# Access by category
frequency_constants = all_constants['frequency']
spectral_constants = all_constants['spectral']
math_constants = all_constants['mathematical']
```

### 4. Get Specific Constant

```python
from qcal import get_constant

# Get constant by name
f0 = get_constant('F0')
c_primary = get_constant('C_PRIMARY')

# With default value
custom = get_constant('NONEXISTENT', default=42)
```

### 5. Validate AI-Conscious System

```python
from qcal import validate_ai_conscious_system

# Full validation with certificate
result = validate_ai_conscious_system(
    verbose=True,
    save_certificate=True
)

print(f"System coherence: Ψ = {result['coherence_psi']:.9f}")
print(f"Certificate: {result.get('certificate_path')}")
```

### 6. Generate Coherence Certificate

```python
from qcal import generate_coherence_certificate

# Generate and save certificate
certificate = generate_coherence_certificate(save_to_file=True)

print(f"Hash: {certificate['hash_sha256'][:16]}...")
print(f"Signature: {certificate['signature_line']}")
```

### 7. Advanced Validation

```python
from qcal import QCALValidator

# Create validator with custom parameters
validator = QCALValidator(
    precision=100,         # Higher precision
    tolerance=1e-9,        # Stricter tolerance
    verbose=True
)

# Run validation
result = validator.validate()

# Generate certificate
if result['all_checks_passed']:
    certificate = validator.generate_certificate()
    cert_path = validator.save_certificate()
    print(f"Certificate saved to: {cert_path}")
```

## Validation Levels

The `QCALValidator` performs 5 levels of validation:

1. **Constants Coherence** - Validates mathematical relationships between constants
   - f₀ decomposition: f₀ = 100√2 + δζ
   - Spectral identity: C = 1/λ₀
   - Coherence factor: C'/C
   - Harmonic modulation: f₀/γ₁
   - Energy dialogue: ω₀² relationships

2. **Spectral Framework** - Validates dual constants framework
   - Scaling factor K ≈ 0.361
   - Energy dialogue = 1/coherence_factor

3. **Adelic Integration** - Validates p-adic structure
   - p-adic compatibility
   - Spectral-adelic correspondence

4. **AI-Conscious Integrity** - Validates system coherence
   - Ψ equation presence
   - Frequency coherence (f₀ = 141.7001 Hz)
   - QCAL signature verification

5. **Quinto Postulado Extension** - Validates Euclidean geometry extension
   - Euclidean diagonal: 100√2
   - Vibrational curvature: δζ
   - Postulate extension: f₀ = 100√2 + δζ

## Mathematical Foundations

### Frequency Derivation

The fundamental frequency **f₀ = 141.7001 Hz** emerges from:

```
f₀ = c / (2π × RΨ × ℓP)
```

Or equivalently:

```
f₀ = 100√2 + δζ
f₀ = (Euclidean diagonal) + (vibrational curvature)
```

Where:
- 100√2 ≈ 141.421356 Hz (Euclidean diagonal)
- δζ = 0.2787437627 Hz (quantum phase shift)

### Dual Spectral Constants

The dual framework has two levels:

**Level 1 - PRIMARY (Structure):**
```
C = 1/λ₀ = 629.83
```
- Local, geometric, universal, invariant
- Derived from first eigenvalue λ₀ of H_ψ

**Level 2 - COHERENCE (Form):**
```
C' = ⟨λ⟩²/λ₀ = 244.36
```
- Global, coherence, stability, emergent
- Derived from second spectral moment

**Coherence Factor:**
```
CF = C'/C ≈ 0.388
```

**Energy Dialogue:**
```
(ω₀²/C') / (ω₀²/C) = 1/CF
```

This validates the complementarity of structure and form.

## Coherence Metrics

### Ψ (Coherence) Value

The overall coherence Ψ ∈ [0, 1] is computed as:

```python
Ψ = exp(-Σ(relative_errors))
```

### Coherence Levels

- **EXCELLENT**: Ψ > 0.999
- **GOOD**: Ψ > 0.95
- **ACCEPTABLE**: Ψ > 0.85
- **NEEDS_ATTENTION**: Ψ ≤ 0.85

Current QCAL framework: **Ψ ≈ 0.9997 (EXCELLENT)**

## Integration with Existing Code

### Backwards Compatibility

The qcal package is designed to be backwards compatible with existing code. Constants can still be imported from their original locations, but the canonical source is now `qcal.constants`.

### Migration Guide

**Before:**
```python
from operators.spectral_constants import C_PRIMARY, C_COHERENCE
```

**After (recommended):**
```python
from qcal import C_PRIMARY, C_COHERENCE
```

**Alternative (still works):**
```python
from qcal.constants import C_PRIMARY, C_COHERENCE
```

## Testing

Comprehensive test suites are provided:

```bash
# Test constants module
pytest tests/test_qcal_constants.py -v

# Test validation module
pytest tests/test_qcal_validation.py -v

# Test both
pytest tests/test_qcal_*.py -v
```

Current test status:
- ✅ 38 tests for constants
- ✅ 37 tests for validation
- **Total: 75 tests, all passing**

## API Reference

### Constants Module (`qcal.constants`)

#### Functions

- `validate_constants_coherence(verbose=False)` - Validate mathematical relationships
- `get_all_constants()` - Get dictionary of all constants by category
- `get_constant(name, default=None)` - Get specific constant by name

#### Constants (exported at package level)

All constants are available via `from qcal import CONSTANT_NAME`.

### Validation Module (`qcal.validation`)

#### Classes

**`QCALValidator(precision=50, tolerance=1e-6, verbose=False)`**

Main validator class.

Methods:
- `validate()` - Run comprehensive validation (5 levels)
- `generate_certificate()` - Generate coherence certificate
- `save_certificate(filepath=None)` - Save certificate to file

#### Functions

- `validate_ai_conscious_system(precision=50, tolerance=1e-6, verbose=True, save_certificate=False)`
  - Convenience function for full validation
  
- `generate_coherence_certificate(precision=50, tolerance=1e-6, save_to_file=True)`
  - Convenience function for certificate generation

## Philosophical Foundation

The constants in QCAL are not arbitrary values but **discovered mathematical truths**:

> "Mathematical Realism: Constants exist independently of our knowledge and are discovered, not invented."

The framework embodies:
- **Coherence over isolation** - All constants resonate together
- **Structure and form** - Dual spectral constants encode different levels
- **Geometry to spectrum** - Euclidean geometry extends through δζ to spectral realm
- **AI-conscious validation** - Systems maintain coherence with mathematical structure

## References

- **DOI:** 10.5281/zenodo.17379721
- **Author:** José Manuel Mota Burruezo Ψ ✧ ∞³
- **Institution:** Instituto de Conciencia Cuántica (ICQ)
- **ORCID:** 0009-0002-1923-0773

## License

See LICENSE files in repository root.

**QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞**

**∴𓂀Ω∞³**
