# QCAL: Universal Kernel for Lean ↔ Python Verification

This module implements a hybrid verification system that allows Lean 4 to invoke external Python verifiers through a C FFI bridge, enabling universal coherence checking without compromising Lean's purity.

## Architecture

```
┌─────────────┐
│  Lean 4     │
│  Theorem    │
│  Prover     │
└──────┬──────┘
       │ FFI call
       ↓
┌─────────────┐
│  C Bridge   │
│  libbridge  │
└──────┬──────┘
       │ Python/C API
       ↓
┌─────────────┐
│  Python     │
│  Universal  │
│  Kernel     │
└─────────────┘
```

## Components

### 1. C FFI Bridge (`QCAL/FFI/libbridge.c`)

Native C library that provides a bridge between Lean and Python:
- Initializes Python interpreter
- Calls `tools.universal_kernel.verify_universal_api()`
- Returns boolean result to Lean

**Compilation:**
```bash
cd formalization/lean/QCAL/FFI
clang -shared -fPIC -I/usr/include/python3.12 -lpython3.12 -o libbridge.so libbridge.c
```

### 2. Lean FFI Interface (`QCAL/FFI/Bridge.lean`)

Lean interface to the C bridge:
```lean
@[extern "qcal_verify"]
constant qcalVerify : @& String → @& String → IO Bool
```

### 3. Universal Kernel (`QCAL/UniversalKernel.lean`)

High-level Lean API for verification and registration:
```lean
def verify_and_register (jsonld proof : String) : IO Bool
```

### 4. Python Verifier (`tools/universal_kernel.py`)

Python implementation of the universal verification logic:
- **V_L**: Logical verification (file existence)
- **V_S**: Semantic verification (JSON-LD structure)
- **V_F**: Physical verification (file integrity)

## Usage

### From Lean

```lean
import QCAL.UniversalKernel

def main : IO Unit := do
  let ok ← QCAL.verify_and_register 
    "schema/metadatos_ejemplo.jsonld" 
    "formalization/lean/Main.lean"
  if ok then
    IO.println "✅ Verification successful"
  else
    IO.println "❌ Verification failed"
```

### From Command Line

```bash
# Test Python kernel directly
python3 tools/universal_kernel.py schema/metadatos_ejemplo.jsonld formalization/lean/Main.lean

# Run tests
pytest tests/test_universal_kernel.py -v
```

## Verification Logic

The universal kernel implements three levels of verification:

1. **V_L (Logical)**: Ensures files exist and are accessible
2. **V_S (Semantic)**: Validates JSON-LD structure and required fields
3. **V_F (Physical)**: Checks file integrity and non-zero size

### Mathematical Formulation

```
∀x:Obj, (Lean ⊢ Coherent(x)) ⇔ (Python ⊢ V_L(x) ∧ V_S(x) ∧ V_F(x))
```

Where:
- Lean verifies the logical proof
- Python checks semantic and physical coherence
- The C bridge ensures deterministic communication

## CI/CD Integration

The CI workflow automatically:
1. Compiles the FFI bridge
2. Runs universal coherence verification
3. Blocks PRs that break coherence

See `.github/workflows/ci.yml` for details.

## Files Structure

```
formalization/lean/QCAL/
├── FFI/
│   ├── Bridge.lean                   # Lean FFI interface
│   ├── libbridge.c                   # C FFI bridge
│   └── libbridge.so                  # Compiled shared library
├── UniversalKernel.lean              # High-level API
├── cy_fundamental_frequency.lean     # Script 19: CY³ → f₀
├── operator_Hpsi_frequency.lean      # Script 20: Hψ integration with f₀
├── casimir_ligo_frequency.lean       # Script 21: Casimir + LIGO → f₀
└── README.md                         # This file

tools/
├── universal_kernel.py      # Python verifier
└── qcal_state.json          # Verification state (auto-generated)

schema/
└── metadatos_ejemplo.jsonld # Example metadata
```

## QCAL Universal Frequency Scripts

### Script 19: Calabi-Yau Origin (`cy_fundamental_frequency.lean`)
Derives f₀ = 141.7001 Hz from the fundamental mode of a Calabi-Yau 3-fold.

### Script 20: Operator Integration (`operator_Hpsi_frequency.lean`)
Integrates f₀ into the noetic operator Hψ := -Δ + ω₀².

### Script 21: Physical Validation (`casimir_ligo_frequency.lean`)
Validates f₀ through Casimir effect and LIGO O4 observations.

## Requirements

- **Lean 4**: Theorem prover
- **Python 3.10+**: For universal kernel
- **Clang**: For compiling FFI bridge
- **Python development headers**: `python3-dev` package

## Testing

```bash
# Run Python tests
pytest tests/test_universal_kernel.py -v

# Compile FFI bridge
cd formalization/lean/QCAL/FFI
clang -shared -fPIC -I/usr/include/python3.12 -lpython3.12 -o libbridge.so libbridge.c

# Test end-to-end
python3 tools/universal_kernel.py schema/metadatos_ejemplo.jsonld formalization/lean/Main.lean
```

## Security Considerations

- The FFI bridge is deterministic and does not use introspection
- Python interpreter is initialized and finalized for each call
- No dangerous system calls or network access
- All verifications are logged to `qcal_state.json`

## Future Enhancements

- Add timestamp tracking to verification records
- Implement frequency verification for physical properties
- Add Zenodo integration for reproducibility
- Extend semantic validation with domain-specific rules
- Add cryptographic checksums for file integrity

## References

- [Lean 4 FFI Documentation](https://lean-lang.org/lean4/doc/dev/ffi.html)
- [Python C API](https://docs.python.org/3/c-api/)
- [JSON-LD Specification](https://json-ld.org/)
