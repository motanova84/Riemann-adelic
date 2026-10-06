# FFI Bridge Setup and Integration Guide

## 🚀 Quick Setup

### Step 1: Install Dependencies

```bash
# Install Python development headers (required for C compilation)
# Ubuntu/Debian
sudo apt-get install python3-dev

# Fedora/RHEL
sudo dnf install python3-devel

# macOS
brew install python
```

### Step 2: Install Python Packages

```bash
# Navigate to repository root
cd /path/to/Riemann-adelic

# Install required Python packages
pip install numpy mpmath

# The QCAL package is already in the repository
# so no additional installation needed
```

### Step 3: Build the FFI Bridge

```bash
# Navigate to FFI directory
cd ffi

# Build the C bridge library
make

# Verify build
ls -lh libffi_bridge.so
```

### Step 4: Test the Bridge

```bash
# Run standalone test (no dependencies)
python3 test_standalone.py

# Run full test suite (requires numpy, mpmath, qcal)
python3 test_ffi.py
```

### Step 5: Set Library Path

```bash
# Temporary (current session only)
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$(pwd)

# Permanent (add to ~/.bashrc or ~/.zshrc)
echo 'export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/path/to/Riemann-adelic/ffi' >> ~/.bashrc
source ~/.bashrc
```

## 🔗 Integration with Lean Build System

### Option 1: Manual Integration

Add the FFI module to your Lean project:

```bash
cd formalization/lean

# Import FFI in your Lean file
echo "import FFI" > test_ffi.lean
echo "#eval FFI.demo" >> test_ffi.lean

# Build
lake build test_ffi
```

### Option 2: Lakefile Integration

Add to `formalization/lean/lakefile.lean`:

```lean
-- FFI library
lean_lib FFI where
  roots := #[`FFI]
  srcDir := "../../ffi"  -- Path to FFI.lean

-- Link the C library
target ffi_bridge.o pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi_bridge.o"
  let srcFile : FilePath := pkg.dir / ".." / ".." / "ffi" / "ffi_bridge.c"
  buildO oFile srcFile #["-I/usr/include/python3.11", "-fPIC"]

extern_lib libffi_bridge pkg := do
  let name := nameToStaticLib "ffi_bridge"
  let ffiO ← fetch <| pkg.target ``ffi_bridge.o
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]
```

### Option 3: System-Wide Installation

```bash
# Build and install the library system-wide
cd ffi
sudo make install

# This installs libffi_bridge.so to /usr/local/lib
# and updates ldconfig
```

## 📋 Usage Patterns

### Pattern 1: Direct FFI Calls

```lean
import FFI

def myProof : IO Unit := do
  -- Get constants directly from Python
  let f0 ← FFI.getF0
  
  -- Use in computations
  if f0 == 141.7001 then
    IO.println "✅ Correct frequency"
```

### Pattern 2: Validation Integration

```lean
import FFI

theorem qcal_coherence_holds : IO Bool := do
  -- Validate QCAL coherence using Python
  FFI.validateCoherence

-- Use in proofs
example : IO Bool := qcal_coherence_holds
```

### Pattern 3: Numerical Verification

```lean
import FFI

def verifyRiemannZero (n : Nat) : IO Bool := do
  match ← FFI.computeRiemannZero n with
  | none => return false
  | some zero =>
      -- Check it's on critical line
      return zero.real == 0.5 ∧ zero.onCriticalLine
```

### Pattern 4: Certificate Generation

```lean
import FFI

def generateProofCertificate : IO Unit := do
  -- Run validation
  let result ← FFI.runValidation 50
  
  -- Generate certificate
  if result.allChecksPassed then
    let ok ← FFI.generateCertificate "data/lean_proof_cert.json"
    if ok then
      IO.println "✅ Certificate generated"
```

## 🔧 Troubleshooting

### Error: "libpython3.X.so: cannot open shared object file"

**Solution:**
```bash
# Find Python library path
python3 -c "import sysconfig; print(sysconfig.get_config_var('LIBDIR'))"

# Add to LD_LIBRARY_PATH
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/lib/python3.11/config
```

### Error: "FFI module not loaded"

**Solution:**
```bash
# Ensure Python can find the module
export PYTHONPATH=$PYTHONPATH:/path/to/Riemann-adelic

# Or add to sys.path in Python
python3 -c "import sys; sys.path.insert(0, '/path/to/Riemann-adelic'); from ffi import python_ffi_wrapper"
```

### Error: "No module named 'qcal'"

**Solution:**
```bash
# The qcal module is in the repository
cd /path/to/Riemann-adelic
export PYTHONPATH=$PYTHONPATH:$(pwd)

# Or create a symbolic link
ln -s /path/to/Riemann-adelic/qcal /usr/local/lib/python3.11/site-packages/qcal
```

### Error: Compilation fails with "Python.h not found"

**Solution:**
```bash
# Install Python development headers
sudo apt-get install python3-dev  # Ubuntu/Debian
sudo dnf install python3-devel    # Fedora/RHEL
brew install python               # macOS
```

### Error: Segmentation fault when calling FFI

**Possible causes:**
1. Python interpreter not initialized
2. Type mismatch between Lean and Python
3. Memory corruption

**Solution:**
```bash
# Enable debugging
export PYTHONVERBOSE=1
export LEAN_DEBUG=1

# Check Python version compatibility
python3 --version
lean --version
```

## 🧪 Testing Strategy

### Level 1: Standalone Test (No Dependencies)

```bash
python3 ffi/test_standalone.py
```

Tests basic infrastructure without external dependencies.

### Level 2: Python Wrapper Test

```bash
python3 ffi/test_ffi.py
```

Tests all FFI functions with full dependencies.

### Level 3: C Bridge Test

```bash
# Create a simple C test program
gcc -o test_bridge ffi/test_bridge.c -Iffi -Lffi -lffi_bridge -lpython3.11
./test_bridge
```

### Level 4: Lean Integration Test

```bash
cd formalization/lean
lake build
lake env lean --run ffi/examples/ffi_example.lean
```

## 📊 Performance Considerations

### Python Interpreter Overhead

- **First call**: ~100ms (interpreter initialization)
- **Subsequent calls**: ~1-10ms per call
- **Large computations**: Dominated by computation time

### Optimization Tips

1. **Batch operations**: Call Python once with multiple computations
2. **Persistent interpreter**: Keep interpreter alive across calls
3. **Preload modules**: Import heavy modules at initialization
4. **Use JSON for complex data**: Avoid multiple small calls

### Example: Batched Zero Computation

```lean
-- Bad: Multiple FFI calls
def computeZerosSlow (n : Nat) : IO (List RiemannZero) := do
  let mut zeros := []
  for i in [1:n+1] do
    match ← FFI.computeRiemannZero i with
    | some z => zeros := z :: zeros
    | none => continue
  return zeros

-- Better: Single FFI call (would need batch API)
def computeZerosFast (n : Nat) : IO (List RiemannZero) := do
  -- Call Python once to compute all n zeros
  FFI.computeRiemannZerosBatch n
```

## 🔐 Security Best Practices

1. **Input Validation**: Always validate data before passing to FFI
2. **Error Handling**: Check return values and handle errors
3. **Resource Limits**: Set timeouts for long computations
4. **Trusted Code**: Only use FFI with trusted Python modules
5. **Memory Management**: Be aware of memory leaks in long-running processes

## 📚 Advanced Topics

### Custom FFI Functions

To add a new FFI function:

1. **Add Python function** in `python_ffi_wrapper.py`:
   ```python
   def ffi_my_function(arg: type) -> returntype:
       # Implementation
       return result
   ```

2. **Add C bridge** in `ffi_bridge.c`:
   ```c
   returntype ffi_my_function(argtype arg) {
       // Call Python function
       return result;
   }
   ```

3. **Add Lean binding** in `FFI.lean`:
   ```lean
   @[extern "ffi_my_function"]
   constant myFunctionImpl : ArgType → ReturnType
   
   def myFunction (arg : ArgType) : IO ReturnType :=
     return myFunctionImpl arg
   ```

4. **Rebuild**:
   ```bash
   cd ffi && make clean && make
   ```

### Async FFI Calls

For long-running computations, use async patterns:

```lean
-- Would require additional infrastructure
def computeZeroAsync (n : Nat) : IO (Task RiemannZero) := do
  -- Spawn async task
  IO.asTask (FFI.computeRiemannZero n)
```

## 🎯 Next Steps

1. **Integrate with CI/CD**: Add FFI tests to GitHub Actions
2. **Extend API**: Add more QCAL functions to FFI
3. **Optimize Performance**: Implement batching and caching
4. **Add More Tests**: Increase test coverage
5. **Documentation**: Add more usage examples

## 📖 References

- [Lean 4 FFI Documentation](https://lean-lang.org/lean4/doc/dev/ffi.html)
- [Python C API](https://docs.python.org/3/c-api/)
- [QCAL Framework](../qcal/README.md)

---

**Need help?** Check the troubleshooting section or open an issue on GitHub.
