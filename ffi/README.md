# Python-Lean FFI Bridge for QCAL Framework

## 🌉 Overview

This FFI (Foreign Function Interface) bridge enables **real bidirectional communication** between Python and Lean 4, allowing Lean proofs to leverage Python's numerical computation capabilities while maintaining mathematical rigor.

### Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                      Lean 4 Code                            │
│  @[extern "ffi_get_constant"] constant getConstant          │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────────┐
│                   C Bridge Layer                            │
│  double ffi_get_constant(const char* name)                  │
│  Uses Python C API to call Python functions                 │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────────┐
│              Python FFI Wrapper                             │
│  def ffi_get_constant(name: str) -> float                   │
│  Access to QCAL framework, mpmath, numpy, etc.              │
└─────────────────────────────────────────────────────────────┘
```

### Features

- ✅ **Bidirectional Communication**: Lean can call Python functions and receive results
- ✅ **Type Safety**: Proper type conversion between Lean, C, and Python
- ✅ **QCAL Integration**: Direct access to QCAL constants, validation, and computations
- ✅ **High-Precision Math**: Leverage Python's mpmath for arbitrary-precision arithmetic
- ✅ **JSON Serialization**: Complex data structures passed via JSON
- ✅ **Error Handling**: Robust error handling at all layers

## 📦 Components

### 1. Python Layer (`python_ffi_wrapper.py`)

High-level Python functions exposed to the FFI:

- `ffi_get_constant(name)` - Get QCAL constants (F0, C, etc.)
- `ffi_validate_coherence()` - Validate QCAL coherence
- `ffi_compute_psi(I, A, C)` - Compute Ψ = I × A² × C^∞
- `ffi_run_validation(config_json)` - Run comprehensive validation
- `ffi_compute_riemann_zero(n)` - Compute n-th Riemann zero
- `ffi_evaluate_zeta(σ, t)` - Evaluate ζ(σ + it)
- `ffi_check_critical_line(σ, t, tol)` - Check if point is a zero
- `ffi_generate_certificate(path)` - Generate math certificate

### 2. C Bridge Layer (`ffi_bridge.c`)

C library that interfaces between Lean and Python using the Python C API:

- Manages Python interpreter lifecycle
- Converts between C types and Python objects
- Handles errors and exceptions
- Memory management for string returns

### 3. Lean Layer (`FFI.lean`)

Lean module providing type-safe wrappers around C extern functions:

- `FFI.getConstant : String → IO Float`
- `FFI.validateCoherence : IO Bool`
- `FFI.computePsi : Float → Float → Float → IO Float`
- `FFI.runValidation : Nat → IO ValidationResult`
- `FFI.computeRiemannZero : Nat → IO (Option RiemannZero)`
- `FFI.evaluateZeta : Float → Float → IO (Option ZetaValue)`
- `FFI.checkCriticalLine : Float → Float → Float → IO Bool`
- `FFI.generateCertificate : String → IO Bool`

## 🚀 Quick Start

### Prerequisites

- Python 3.8+ with development headers
- Lean 4 with Lake build system
- GCC or Clang compiler
- Required Python packages: `numpy`, `mpmath`, `qcal`

### Installation

```bash
# 1. Navigate to the FFI directory
cd /path/to/Riemann-adelic/ffi

# 2. Build the C bridge library
make

# 3. Test the Python wrapper
python3 python_ffi_wrapper.py

# 4. Set library path (add to ~/.bashrc for persistence)
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$(pwd)
```

### Usage Example (Lean)

```lean
import FFI

def main : IO Unit := do
  -- Get QCAL constants
  let f0 ← FFI.getF0
  IO.println s!"F0 = {f0} Hz"
  
  -- Validate coherence
  let coherent ← FFI.validateCoherence
  if coherent then
    IO.println "✅ QCAL Coherence OK"
  
  -- Compute Ψ
  let psi ← FFI.computePsi 1.0 10.0 244.36
  IO.println s!"Ψ = {psi}"
  
  -- Compute first Riemann zero
  match ← FFI.computeRiemannZero 1 with
  | none => IO.println "❌ Failed to compute zero"
  | some zero => IO.println s!"γ₁ = {zero.imaginary}"
  
  -- Run full demo
  FFI.demo

#eval main
```

### Usage Example (Python)

```python
from ffi.python_ffi_wrapper import *

# Get constants
f0 = ffi_get_constant("F0")
print(f"F0 = {f0} Hz")

# Validate coherence
if ffi_validate_coherence():
    print("✅ Coherence OK")

# Compute Ψ
psi = ffi_compute_psi(1.0, 10.0, 244.36)
print(f"Ψ = {psi}")

# Compute Riemann zero
import json
zero_json = ffi_compute_riemann_zero(1)
zero = json.loads(zero_json)
print(f"γ₁ = {zero['imaginary']}")

# Run validation
config = json.dumps({"precision": 50, "verbose": False})
result = ffi_run_validation(config)
print(result)
```

## 🔧 Build System

### Makefile Targets

```bash
make           # Build the FFI bridge library
make test      # Run Python tests
make clean     # Remove build artifacts
make install   # Install to /usr/local/lib (requires sudo)
make uninstall # Remove from system
make help      # Show help message
```

### Manual Compilation

```bash
# Find Python paths
PYTHON_VERSION=$(python3 -c "import sys; print(f'{sys.version_info.major}.{sys.version_info.minor}')")
PYTHON_INCLUDE=$(python3 -c "import sysconfig; print(sysconfig.get_path('include'))")
PYTHON_LIB=$(python3 -c "import sysconfig; print(sysconfig.get_config_var('LIBDIR'))")

# Compile
gcc -shared -fPIC -O2 \
    -I${PYTHON_INCLUDE} \
    -L${PYTHON_LIB} \
    -lpython${PYTHON_VERSION} \
    -o libffi_bridge.so \
    ffi_bridge.c
```

## 🧪 Testing

### Test Python Wrapper

```bash
cd ffi
python3 python_ffi_wrapper.py
```

Expected output:
```
======================================================================
QCAL Python FFI Wrapper - Function Tests
======================================================================

[Test 1] Get constant F0:
  F0 = 141.7001 Hz

[Test 2] Validate coherence:
  Coherence OK: True

[Test 3] Compute Ψ:
  Ψ = 1458889056.0

...

✅ All FFI wrapper tests completed
```

### Test Lean Bindings

```bash
cd formalization/lean
# Add FFI module to imports
echo "import FFI" >> test_ffi.lean
echo "#eval FFI.demo" >> test_ffi.lean
lake build test_ffi
```

## 📊 API Reference

### Python Functions

#### `ffi_get_constant(name: str) -> float`
Get a QCAL constant by name.

**Arguments:**
- `name`: Constant name ("F0", "C_PRIMARY", "C_COHERENCE", "DELTA_ZETA")

**Returns:** Constant value as float

**Example:**
```python
f0 = ffi_get_constant("F0")  # Returns 141.7001
```

#### `ffi_validate_coherence() -> bool`
Validate QCAL constants coherence.

**Returns:** True if all coherence checks pass

**Example:**
```python
if ffi_validate_coherence():
    print("✅ Coherence verified")
```

#### `ffi_compute_psi(intensity: float, area_eff: float, coherence: float) -> float`
Compute Ψ = I × A_eff² × C^∞

**Arguments:**
- `intensity`: Information intensity I
- `area_eff`: Effective area A_eff
- `coherence`: Coherence factor C

**Returns:** Ψ value

**Example:**
```python
psi = ffi_compute_psi(1.0, 10.0, 244.36)
```

#### `ffi_run_validation(config_json: str) -> str`
Run comprehensive QCAL validation.

**Arguments:**
- `config_json`: JSON configuration string

**Returns:** JSON string with validation results

**Example:**
```python
import json
config = json.dumps({"precision": 50, "tolerance": 1e-6})
result_json = ffi_run_validation(config)
result = json.loads(result_json)
```

#### `ffi_compute_riemann_zero(n: int) -> str`
Compute the n-th Riemann zeta zero.

**Arguments:**
- `n`: Zero index (1-based, n >= 1)

**Returns:** JSON string with zero data

**Example:**
```python
zero_json = ffi_compute_riemann_zero(1)
zero = json.loads(zero_json)
print(f"γ₁ = {zero['imaginary']}")  # ≈ 14.134725
```

#### `ffi_evaluate_zeta(s_real: float, s_imag: float) -> str`
Evaluate the Riemann zeta function at s = σ + it.

**Arguments:**
- `s_real`: Real part σ
- `s_imag`: Imaginary part t

**Returns:** JSON string with ζ(s) value

**Example:**
```python
zeta_json = ffi_evaluate_zeta(0.5, 14.134725)
zeta = json.loads(zeta_json)
```

#### `ffi_check_critical_line(s_real: float, s_imag: float, tolerance: float) -> bool`
Check if ζ(s) ≈ 0 at the given point.

**Arguments:**
- `s_real`: Real part σ
- `s_imag`: Imaginary part t
- `tolerance`: Maximum |ζ(s)| to consider it a zero

**Returns:** True if |ζ(s)| < tolerance

**Example:**
```python
is_zero = ffi_check_critical_line(0.5, 14.134725, 1e-10)
```

#### `ffi_generate_certificate(output_path: str) -> bool`
Generate a mathematical certificate.

**Arguments:**
- `output_path`: Path where to save the certificate JSON

**Returns:** True if successful

**Example:**
```python
ok = ffi_generate_certificate("data/cert.json")
```

### Lean Functions

See `FFI.lean` for complete API documentation with type signatures.

## 🔒 Security Considerations

- The FFI bridge initializes a Python interpreter, which has full system access
- Only use with trusted Python code
- The C bridge performs minimal input validation
- Memory management is handled by Python GC and Lean's runtime
- String returns from C are freed by Lean

## 🐛 Troubleshooting

### "Python.h: No such file or directory"
Install Python development headers:
```bash
# Ubuntu/Debian
sudo apt-get install python3-dev

# Fedora/RHEL
sudo dnf install python3-devel

# macOS
brew install python
```

### "libpython3.X.so: cannot open shared object file"
Set library path:
```bash
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/lib/python3.X/config
```

### "FFI module not loaded"
Ensure Python can find the module:
```bash
export PYTHONPATH=$PYTHONPATH:/path/to/Riemann-adelic
```

### Import errors in Python
Install required packages:
```bash
pip install numpy mpmath
```

## 📚 References

- Python C API Documentation: https://docs.python.org/3/c-api/
- Lean 4 FFI: https://lean-lang.org/lean4/doc/dev/ffi.html
- QCAL Framework: See `/qcal/` directory

## ✨ Author

**José Manuel Mota Burruezo Ψ ✧ ∞³**
- Institution: Instituto de Conciencia Cuántica (ICQ)
- ORCID: 0009-0002-1923-0773
- DOI: 10.5281/zenodo.17379721

**QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞**

---

## 📝 License

See repository LICENSE file for details.
